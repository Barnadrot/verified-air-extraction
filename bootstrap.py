"""Fetch the pinned dependencies for the Linux x86-64 proof build."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
BUILD = ROOT / "proofs/divrem"
CAPTURE = ROOT / "proofs/capture"
TOOLS = ROOT / "work/tools/linux"
PIN = "b09644c2004b11847c8d24e57d14e34bb02e3d06"
MODEL = "51c635c460125ac87955d061fcd902ce03b8011f"
RUNTIME = "079463134b9c50450b8393e1566a09fc492a34d9"


def run(*args, cwd=ROOT, env=None):
    subprocess.run([str(a) for a in args], cwd=cwd, env=env, check=True)


def checkout(url, pin, path):
    if not path.exists():
        path.mkdir(parents=True)
        run("git", "init", "--quiet", path)
        run("git", "-C", path, "remote", "add", "origin", url)
    if not (path / ".git").exists():
        raise RuntimeError(f"Expected a pinned Git checkout: {path}")
    result = subprocess.run(["git", "-C", str(path), "cat-file", "-e", pin + "^{commit}"],
                            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    if result.returncode:
        run("git", "-C", path, "fetch", "--depth=1", "origin", pin)
    current = subprocess.run(["git", "-C", str(path), "rev-parse", "HEAD"],
                             capture_output=True, text=True)
    if current.returncode:
        run("git", "-C", path, "-c", "core.autocrlf=false", "checkout", "--detach", pin)
    elif current.stdout.strip() != pin:
        raise RuntimeError(f"Existing checkout has another revision: {path}")
    return path


def verify_tree(path, allowed=()):
    """Check upstream blobs, allowing only the explicitly listed local files."""
    tree = subprocess.check_output(["git", "-C", str(path), "ls-tree", "-rz", "HEAD"])
    for record in tree.split(b"\0"):
        if not record:
            continue
        metadata, raw_name = record.split(b"\t", 1)
        if metadata.split()[1] != b"blob":
            continue
        name = raw_name.decode()
        if name in allowed:
            continue
        content = (os.readlink(path / name).encode() if (path / name).is_symlink()
                   else (path / name).read_bytes())
        expected = metadata.split()[2].decode()
        variants = (content, content.replace(b"\r\n", b"\n"))
        if not any(hashlib.sha1(b"blob " + str(len(v)).encode() + b"\0" + v).hexdigest() == expected
                   for v in variants):
            raise RuntimeError(f"Dependency content differs from its pin: {path}/{name}")


def main():
    run(sys.executable, BUILD / "bootstrap_linux.py")
    lineth = checkout("https://github.com/LFDT-Lineth/lineth-monorepo.git",
                      "2737d8c6b0cdba2b54c195aa6c10958538c5f3e4", ROOT / "work/lineth-snapshot")
    verify_tree(lineth)
    base = ROOT / "work/sail-reference"
    runtime = checkout("https://github.com/rems-project/lean-sail.git", RUNTIME,
                       base / ("lean-sail-" + RUNTIME))
    verify_tree(runtime)
    model = checkout("https://github.com/opencompl/sail-riscv-lean.git", MODEL,
                     base / ("sail-riscv-lean-" + MODEL))
    # The published model's v5 runtime reference is replaced by the exact pinned
    # sibling checkout. No generated model or runtime Lean definition is edited.
    verify_tree(model, {"lakefile.toml", "lake-manifest.json"})
    original = subprocess.check_output(["git", "-C", str(model), "show", "HEAD:lakefile.toml"]).decode()
    replacement = original.replace('git = "https://github.com/rems-project/lean-sail"',
                                   'path = "../lean-sail-' + RUNTIME + '"')
    replacement = replacement.replace('\nrev = "v5"', '')
    (model / "lakefile.toml").write_text(replacement)
    perennial = checkout("https://github.com/mit-pdos/perennial.git", PIN, CAPTURE / "perennial")
    patches = json.loads((CAPTURE / "translator-patch-files.json").read_text(encoding="utf-8-sig"))
    verify_tree(perennial, patches)
    for name, expected in patches.items():
        source = ROOT / "patches/perennial" / name
        if hashlib.sha256(source.read_bytes()).hexdigest().upper() != expected:
            raise RuntimeError("Translator patch checksum differs: " + name)
        target = perennial / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    env = dict(os.environ, PATH=str(TOOLS / "go-1.27.1/bin") + os.pathsep + os.environ["PATH"],
               GOTOOLCHAIN="local", GOPATH=str(ROOT / "work/go-path"),
               GOMODCACHE=str(ROOT / "work/go-modules"), GOCACHE=str(ROOT / "work/go-cache-linux"),
               GOWORK=str(BUILD / "go.work"), MATHLIB_CACHE_DIR=str(ROOT / "work/mathlib-cache"))
    run(TOOLS / "go-1.27.1/bin/go", "mod", "download", cwd=BUILD, env=env)
    run(TOOLS / "go-1.27.1/bin/go", "mod", "download", cwd=perennial,
        env=dict(env, GOWORK="off"))
    # Fetch the dependency graph recorded in each Lake manifest. Never use
    # `lake update`, which can change inherited revision pins.
    for package, version in ((BUILD, "4.30.0"), (CAPTURE, "4.34.1")):
        manifest = json.loads((package / "lake-manifest.json").read_text())
        for dep in manifest["packages"]:
            if dep["type"] == "git":
                dependency = checkout(dep["url"], dep["rev"], package / ".lake/packages" / dep["name"])
                verify_tree(dependency)
        lake = TOOLS / ("lean-" + version + "-linux/bin/lake")
        stage_env = dict(env, PATH=str(lake.parent) + os.pathsep + env["PATH"])
        run(lake, "env", "lean", "--version", cwd=package, env=stage_env)
    main_env = dict(env, PATH=str(TOOLS / "lean-4.30.0-linux/bin") + os.pathsep + env["PATH"])
    run(TOOLS / "lean-4.30.0-linux/bin/lake", "exe", "cache", "get", cwd=BUILD, env=main_env)
    print("Pinned dependencies ready. Run: bash build.sh", flush=True)


if __name__ == "__main__":
    main()
