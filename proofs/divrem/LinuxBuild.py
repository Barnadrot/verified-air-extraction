"""Fedora/Linux counterpart of Build.ps1. Proof targets and allowed axioms stay fixed."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re
import shutil
import signal
import subprocess
import sys

BUILD = Path(__file__).resolve().parent
ROOT = BUILD.parent.parent
SOURCE = ROOT / "proofs/capture"
TOOLS = ROOT / "work/tools/linux"
LOG = BUILD / "artifacts/linux"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
GO = TOOLS / "go-1.27.1/bin/go"
LAKE = TOOLS / "lean-4.30.0-linux/bin/lake"
SOURCE_LAKE = TOOLS / "lean-4.34.1-linux/bin/lake"
STAMP = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%SZ")

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def load(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))

def put(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n")

def windows_native(path):
    with path.open("rb") as source:
        head = source.read(8)
        if head != b"!<arch>\n":
            return head[:2] in (b"\x64\x86", b"\x00\x00")
        while header := source.read(60):
            if len(header) != 60:
                return False
            name = header[:16].strip()
            size = int(header[48:58])
            start = source.tell()
            if name not in (b"/", b"//", b"/SYM64/"):
                if name.startswith(b"#1/"):
                    source.seek(int(name[3:]), 1)
                signature = source.read(4)
                if signature == b"\x7fELF":
                    return False
                if signature[:2] in (b"\x64\x86", b"\x00\x00"):
                    return True
            source.seek(start + size + size % 2)
    return False

class Runner:
    def __init__(self, args):
        self.args = args
        LOG.mkdir(parents=True, exist_ok=True)
        self.env = dict(os.environ, PATH=str(GO.parent) + os.pathsep + os.environ["PATH"],
                        GOTOOLCHAIN="local", GOPATH=str(ROOT / "work/go-path"),
                        GOMODCACHE=str(ROOT / "work/go-modules"),
                        GOCACHE=str(ROOT / "work/go-cache-linux"), GOWORK=str(BUILD / "go.work"),
                        LEAN_NUM_THREADS="4")
        self.protected = {str(p.relative_to(ROOT)): sha(p) for p in
                          (ROOT / "docs/spec.md", BUILD / "DivRemFV/Statement.lean",
                           BUILD / "DivRemFV/SignedInterface64.lean", BUILD / "DivRemFV/ComponentBoundary64.lean")}
        self.state = {"platform": "linux", "status": "running", "started_utc": STAMP,
                      "stage": args.stage, "steps": [], "protected_inputs": self.protected,
                      "proof_rebuild": "root build outputs moved aside" if args.clean else "Lake incremental build with rehashed inputs",
                      "scope": "signed RV64 helper and capture contracts, with raw-input and real call-site extension; no production guarantee"}
        self.save()

    def save(self):
        put(LOG / "build-status.json", self.state)

    def run(self, name, cmd, cwd=BUILD, env=None, expected=0):
        print(name, flush=True)
        path = LOG / (name + ".log")
        self.state["current_step"] = name
        self.save()
        with path.open("w") as output:
            execution_env = dict(env or self.env)
            if str(cmd[0]) in (str(LAKE), str(SOURCE_LAKE)):
                execution_env["PATH"] = str(Path(cmd[0]).parent) + os.pathsep + execution_env["PATH"]
            result = subprocess.run([str(x) for x in cmd], cwd=cwd, env=execution_env,
                                    stdout=output, stderr=subprocess.STDOUT)
        self.state["steps"].append({"name": name, "exit_code": result.returncode, "log": str(path.relative_to(BUILD))})
        self.save()
        if result.returncode != expected:
            print("\n".join(path.read_text(errors="replace").splitlines()[-35:]), flush=True)
            raise RuntimeError(f"{name}: exit {result.returncode}, expected {expected}")
        return path.read_text(errors="replace")

    def audit(self, name, source, lake, cwd):
        text = self.run(name, [lake, "env", "lean", source], cwd=cwd)
        required = re.findall(r"#print axioms ([^\r\n]+)", (cwd / source).read_text())
        reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", text)
        found = {n: {a.strip() for a in ax.split(",") if a.strip()} for n, ax in reports}
        if not required or not set(required) <= set(found) or any(found[n] - ALLOWED for n in required):
            raise RuntimeError(f"{name}: missing endpoint or unapproved axiom")

    def preflight(self):
        for tool in (GO, LAKE, SOURCE_LAKE):
            if not os.access(tool, os.X_OK):
                raise RuntimeError(f"Pinned Linux toolchain absent: {tool}. Run python3 bootstrap_linux.py first.")
        for name, tool, expected in (("go-version", GO, "go1.27.1"), ("lean-version", LAKE, "4.30.0"), ("source-lean-version", SOURCE_LAKE, "4.34.1")):
            text = self.run(name, [tool, "version" if tool == GO else "--version"])
            if expected not in text:
                raise RuntimeError(f"{name}: wrong version")
        if self.args.clean:
            directories = ([BUILD / ".lake/build"] if self.args.stage == "main" else
                           [SOURCE / ".lake/build"] if self.args.stage == "capture" else
                           [BUILD / ".lake/build", SOURCE / ".lake/build"])
            for directory in directories:
                if directory.exists():
                    directory.rename(directory.with_name("build-before-linux-" + STAMP))
        # Native Windows objects cannot be linked into Linux binaries. Keep a
        # reversible copy, and let Lake rebuild them from the same C sources.
        moved = 0
        for base in (BUILD / ".lake/packages", ROOT / "work/sail-reference"):
            for path in base.rglob("*"):
                if not path.is_file() or ".lake/build/" not in path.as_posix():
                    continue
                if path.name.endswith((".o", ".o.export", ".o.noexport", ".a")):
                    if windows_native(path):
                        path.rename(path.with_name(path.name + ".before-linux-" + STAMP))
                        moved += 1
        self.state["preserved_imported_native_objects"] = moved
        self.save()

    def main_build(self):
        self.run("go-tests", [GO, "test", "./...", "-v", "-count=1"])
        self.run("go-vet", [GO, "vet", "./..."])
        self.run("export-air", [GO, "run", "./cmd/export-air"])
        self.run("reify-air", [GO, "run", "./cmd/reify-air"])
        self.run("constraint-mutation", [GO, "run", "./cmd/check-mutation"])
        self.run("build-binder", [LAKE, "--rehash", "build", "air_bind"])
        self.run("bind-json", [BUILD / ".lake/build/bin/air_bind", "artifacts/air.json", "artifacts/divrem-air.json", "artifacts/helper-interfaces.json", "DivRemFV/CapturedData.lean"])
        self.run("build-main", [LAKE, "--rehash", "build"])
        self.run("build-trace-semantics", [LAKE, "build", "trace_semantics"])
        self.audit("trace-axioms", "TraceAudit.lean", LAKE, BUILD)
        self.run("trace-semantics", [GO, "test", "./internal/airdata", "-run", "^TestTraceSemanticsAgainstZkC$",
                  "-count=1", "-timeout=60m", "-v"],
                 env=dict(self.env, DIVREM_SEMANTICS_EXE=str(BUILD / ".lake/build/bin/trace_semantics")))
        self.run("generate-replay", [sys.executable, "replay_wire.py"])
        manifest = load(BUILD / "artifacts/replay-manifest.json")
        parts = ["DivRemFV.Replay." + n for n in manifest["parts"]]
        for offset in range(0, len(parts), 8):
            self.run(f"replay-{offset:03d}", [LAKE, "build", *parts[offset:offset+8]])
        self.run("build-final-binding", [LAKE, "build", "DivRemFV.ExtractorBinding", "replay_input_check"])
        snippet = re.search(r"```lean\n(.*?)\n```", (ROOT / "README.md").read_text(), re.S)
        if snippet is None:
            raise RuntimeError("README theorem example missing")
        example = BUILD / "artifacts/ReadmeExample.lean"
        example.write_text(snippet.group(1) + "\n")
        self.run("readme-example", [LAKE, "env", "lean", example])
        for name, source in (("replay-axioms", "ReplayAudit.lean"), ("statement-axioms", "StatementAudit.lean"),
                             ("interface-axioms", "InterfaceAudit.lean"),
                             ("arithmetic-axioms", "Audit.lean"), ("term-wire-axioms", "TermWireAudit.lean"),
                             ("artifact-axioms", "ArtifactAudit.lean")):
            self.audit(name, source, LAKE, BUILD)
        self.run("input-identity", [BUILD / ".lake/build/bin/replay_input_check", "artifacts/air.wire"])
        self.run("term-vectors", [BUILD / ".lake/build/bin/term_wire_reader", "artifacts/term-wire-vectors.json"])
        self.run("read-helper", [BUILD / ".lake/build/bin/air_reader", "artifacts/divrem-air.json"])
        self.run("expression-vectors", [BUILD / ".lake/build/bin/air_reader", "--vectors", "artifacts/expression-vectors.json"])
        self.run("json-binding-mutations", [GO, "run", "./cmd/check-binding"])
        self.run("wire-binding-mutations", [GO, "run", "./cmd/check-wire-binding"])
        self.run("wire-decoder-mutations", [sys.executable, "check_wire_mutations.py"])
        self.run("negative-fixtures", [GO, "run", "./cmd/negative-data"])
        for path in sorted((BUILD / "artifacts/negative").glob("*.json")):
            self.run("negative-" + path.stem, [BUILD / ".lake/build/bin/air_reader", path], expected=1)
        self.run("negative-expressions", [BUILD / ".lake/build/bin/air_reader", "--vectors", "artifacts/negative-expression.json"], expected=1)
        self.state["main_claims"] = "passed: helper, full binary replay, final binding, input identity, axioms and executable mutations"
        self.save()

    def translator(self):
        repo = SOURCE / "perennial"
        pin = "b09644c2004b11847c8d24e57d14e34bb02e3d06"
        head = subprocess.check_output(["git", "-C", repo, "rev-parse", "HEAD"], text=True).strip()
        if head != pin:
            raise RuntimeError("Perennial revision changed")
        patches = load(SOURCE / "translator-patch-files.json")
        for name, expected in patches.items():
            if sha(repo / name).upper() != expected.upper():
                raise RuntimeError("Reviewed translator patch changed: " + name)
        # The imported checkout has CRLF differences. Verify content against the
        # pinned tree after CRLF normalization, without changing those files.
        tree = subprocess.check_output(["git", "-C", repo, "ls-tree", "-rz", "HEAD"])
        for record in tree.split(b"\0"):
            if not record: continue
            metadata, name = record.split(b"\t", 1)
            if metadata.split()[1] != b"blob": continue
            name = name.decode()
            if name in patches: continue
            path = repo / name
            content = os.readlink(path).encode() if path.is_symlink() else path.read_bytes()
            expected = metadata.split()[2].decode()
            variants = (content, content.replace(b"\r\n", b"\n"))
            if not any(hashlib.sha1(b"blob " + str(len(v)).encode() + b"\0" + v).hexdigest() == expected
                       for v in variants):
                raise RuntimeError("Unreviewed translator/framework content change: " + name)
        env = dict(self.env, GOWORK="off")
        self.run("translator-tests", [GO, "test", "./goose", "-run", "^TestPackageIDWithShadowedBasename$|^TestExamples/array$", "-count=1"], cwd=repo, env=env)
        for name in ("goose", "perennial-order"):
            self.run("build-" + name, [GO, "build", "-o", LOG / name, "./goose/cmd/" + name], cwd=repo, env=env)

    def translate(self, closure=True):
        if closure:
            packages = [p for p in (SOURCE / "capture-package-closure.txt").read_text().splitlines()
                        if p == "divremfv/internal/airdata" or p.startswith("github.com/LFDT-Lineth/zkc/") and
                        ("/pkg/util/field/" not in p or p.endswith("/koalabear"))]
            packages += ["math", "math/bits", "math/big", "iter"]
            config, dest, prefix = SOURCE / "ClosureConfig", SOURCE / "ClosureGenerated", "CaptureClosure"
            imports = '["github.com/LFDT-Lineth/zkc/*", "math", "math/big", "math/bits", "fmt", "io", "strings", "bytes", "cmp", "errors", "iter"]'
            for package in packages:
                relative = package.replace("github.com", "github_com").replace(".", "_").replace("-", "_") + ".toml"
                original = SOURCE / "Config" / relative
                contents = original.read_text(encoding="utf-8-sig") if original.exists() else 'translate = ["!*"]\ntranslate_types = true\ntrusted = []\ntrust_proofgen = false\n'
                if package == "github.com/LFDT-Lineth/zkc/pkg/schema":
                    contents = re.sub(r"(?m)^translate\s*=.*$", 'translate = ["Table", "UniformSchema", "Constraint", "Assignment", "Table*.Name", "Table*.IsStatic", "Table*.IsNative", "Table*.Registers", "Table*.StaticContents", "Table*.RawConstraints", "UniformSchema*.RawModules"]', contents)
                elif package == "github.com/LFDT-Lineth/zkc/pkg/schema/module":
                    contents = re.sub(r"(?m)^translate\s*=.*$", 'translate = ["Name"]', contents)
                if package in ("math/big", "iter"):
                    contents = re.sub(r"(?m)^imports\s*=.*$", '', contents) + '\nimports = ["!*"]\n'
                elif not re.search(r"(?m)^imports\s*=", contents):
                    contents += "\nimports = " + imports + "\n"
                if package == "github.com/LFDT-Lineth/zkc/pkg/util/field":
                    contents = re.sub(r"(?m)^imports\s*=.*$", 'imports = ["math/big", "github.com/LFDT-Lineth/zkc/pkg/util/word"]', contents)
                target = config / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text(contents)
        else:
            packages = ["math", "math/bits", "github.com/LFDT-Lineth/zkc/pkg/trace", "github.com/LFDT-Lineth/zkc/pkg/util/field/koalabear", "divremfv/internal/airdata"]
            config, dest, prefix = SOURCE / "Config", SOURCE / "Generated", "AirCapture"
        cmd = [LOG / "goose", "-out", dest, "-configdir", config]
        for root in ("github.com/LFDT-Lineth/zkc", "divremfv", "math") + (("iter",) if closure else ()):
            cmd += ["-lean-root", root + "=" + prefix]
        cmd += ["-dir", BUILD, *packages]
        self.run("translate-closure" if closure else "translate-leaves", cmd, cwd=SOURCE)
        if not closure:
            for source in config.rglob("*.toml"):
                target = dest / source.relative_to(config)
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source, target)
        if closure:
            files = dest.rglob("*.lean")
        else:
            files = [dest / p for p in ("math.lean", "math/bits.lean", "github_com/LFDT_Lineth/zkc/pkg/trace.lean", "github_com/LFDT_Lineth/zkc/pkg/util/field/koalabear.lean")]
        for source in files:
            target = SOURCE / prefix / "Code" / source.relative_to(dest)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)

    def capture_build(self):
        self.translator()
        self.translate(closure=False)
        self.run("build-field-index", [SOURCE_LAKE, "--rehash", "build", "AirCapture"], cwd=SOURCE)
        self.audit("field-index-axioms", "AirCapture/Audit.lean", SOURCE_LAKE, SOURCE)
        self.run("ordered-capture-tests", [GO, "test", "-toolexec=" + str(LOG / "perennial-order") + " -code " + str(SOURCE / "Generated"), "./internal/airdata", "-v", "-count=1"])
        self.translate()
        self.run("build-source-getters", [SOURCE_LAKE, "--rehash", "build", "CaptureClosure.Code.divremfv.internal.airdata", "CaptureClosure.Proof.TableReads", "CaptureClosure.Proof.SchemaReads"], cwd=SOURCE)
        self.audit("getter-axioms", "CaptureClosure/Audit.lean", SOURCE_LAKE, SOURCE)
        syntax = (BUILD / "DivRemFV/CaptureSyntax.lean").read_text()
        expected = "module\npublic import Std\n\n@[expose] public section\n" + re.sub(r"^import Std\n", "", syntax)
        if expected.strip() != (SOURCE / "CaptureSyntax.lean").read_text().strip():
            raise RuntimeError("Shared syntax differs between proof builds")
        for script in ("source_loop.py", "columns_wire.py", "list_wire.py", "port_capture_lists.py", "source_contract.py"):
            self.run("prepare-" + Path(script).stem, [sys.executable, script], cwd=SOURCE)
        self.run("build-source-contract", [SOURCE_LAKE, "build", "CaptureClosure.Proof.SourceContract", "CaptureClosure.Proof.ConstraintRejection", "CaptureClosure.Proof.Rejection"], cwd=SOURCE)
        self.audit("source-axioms", "CaptureClosure/PartsAudit.lean", SOURCE_LAKE, SOURCE)
        self.source_mutation()
        self.state["source_claims"] = "passed: actual-source capture, writer, field/index proofs, source axioms and selector mutation with restoration"
        self.save()

    def source_mutation(self):
        source = BUILD / "internal/airdata/export.go"
        translated = SOURCE / "CaptureClosure/Code/divremfv/internal/airdata.lean"
        original, baseline_code = source.read_bytes(), translated.read_bytes()
        needle = b"out.Selector = uintRef(v.Selector.Unwrap())"
        if original.count(needle) != 1:
            raise RuntimeError("Selector mutation point changed")
        mutant = original.replace(needle, b"out.Selector = nil")
        backup = LOG / "mutation-backup"
        backup.mkdir(exist_ok=True)
        (backup / "export.go.txt").write_bytes(original)
        (backup / "airdata.lean.txt").write_bytes(baseline_code)
        try:
            source.write_bytes(mutant)
            self.translate()
            if translated.read_bytes() == baseline_code:
                raise RuntimeError("Source mutation did not reach translated code")
            (backup / "mutant-export.go.txt").write_bytes(mutant)
            (backup / "mutant-airdata.lean.txt").write_bytes(translated.read_bytes())
            self.state["selector_source_mutation"] = {
                "baseline_source_sha256": hashlib.sha256(original).hexdigest(),
                "mutant_source_sha256": hashlib.sha256(mutant).hexdigest(),
                "baseline_translation_sha256": hashlib.sha256(baseline_code).hexdigest(),
                "mutant_translation_sha256": sha(translated),
                "status": "mutation reached translated source; rejection pending"}
            self.save()
            self.run("build-mutant-code", [SOURCE_LAKE, "build", "CaptureClosure.Code.divremfv.internal.airdata"], cwd=SOURCE)
            diagnostic = self.run("reject-mutant-proof", [SOURCE_LAKE, "build", "CaptureClosure.Proof.LookupCapture"], cwd=SOURCE, expected=1)
            if "LookupCapture.lean" not in diagnostic or not any(s in diagnostic for s in ("wp_apply:", "iframe: cannot frame")):
                raise RuntimeError("Wrong source mutation failure")
        finally:
            if source.read_bytes() not in (original, mutant):
                raise RuntimeError("Concurrent capture edit found. Backup retained; no overwrite performed.")
            source.write_bytes(original)
            self.translate()
            if translated.read_bytes() != baseline_code:
                raise RuntimeError("Source translation did not restore exactly")
            self.run("restore-source-contract", [SOURCE_LAKE, "build", "CaptureClosure.Proof.SourceContract", "CaptureClosure.Proof.ConstraintRejection", "CaptureClosure.Proof.Rejection"], cwd=SOURCE)
        self.audit("restored-source-axioms", "CaptureClosure/PartsAudit.lean", SOURCE_LAKE, SOURCE)
        self.run("restored-go-tests", [GO, "test", "./internal/airdata", "-v", "-count=1"])
        self.state["selector_source_mutation"].update(status="passed", source_restored=True, translation_restored=True)
        self.save()

    def finish(self):
        for name, expected in self.protected.items():
            if sha(ROOT / name) != expected:
                raise RuntimeError("Protected spec/target changed: " + name)
        self.state.update(status="passed", completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                          specification_unchanged=True, target_unchanged=True,
                          wire_sha256=sha(BUILD / "artifacts/air.wire"),
                          toolchains=load(TOOLS / "toolchains.json"))
        self.save()
        print("Linux checks passed. Evidence: " + str(LOG / "build-status.json"), flush=True)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", choices=("all", "main", "capture"), default="all")
    parser.add_argument("--clean", action="store_true", help="Preserve and move aside root build caches before recompiling")
    args = parser.parse_args()
    runner = Runner(args)
    try:
        runner.preflight()
        if args.stage in ("all", "main"): runner.main_build()
        if args.stage in ("all", "capture"): runner.capture_build()
        runner.finish()
    except BaseException as error:
        runner.state.update(status="failed", error=str(error))
        runner.save()
        raise

if __name__ == "__main__":
    def interrupted(_number, _frame):
        raise KeyboardInterrupt("Build interrupted; source mutation cleanup will run")
    signal.signal(signal.SIGTERM, interrupted)
    main()
