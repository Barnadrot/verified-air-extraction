"""Install the pinned Linux x86-64 toolchains inside the task workspace."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import hashlib
import json
import platform
import subprocess

ROOT = Path(__file__).resolve().parents[2]
TOOLS = ROOT / "work/tools/linux"
DOWNLOADS = TOOLS / "downloads"
RELEASES = [
    ("lean-4.30.0-linux.tar.zst", "https://github.com/leanprover/lean4/releases/download/v4.30.0/lean-4.30.0-linux.tar.zst",
     "4dad74141c2c119ca1aa626656be83b8e14238afba97271fd7bf1eb3f081b319", TOOLS, False),
    ("lean-4.34.1-linux.tar.zst", "https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-linux.tar.zst",
     "47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4", TOOLS, False),
    ("go1.27.1.linux-amd64.tar.gz", "https://go.dev/dl/go1.27.1.linux-amd64.tar.gz",
     "63d339f0da5ab53635a56f2490a7984dfe12dfcff22ad749f63edaf590168445", TOOLS / "go-1.27.1", True),
]

def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(8 * 1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()

def install(release):
    name, url, expected, destination, strip = release
    archive = DOWNLOADS / name
    if not archive.exists():
        partial = DOWNLOADS / (name + ".part")
        subprocess.run(["curl", "--fail", "--location", "--retry", "3", "--max-time", "900",
                        "--silent", "--show-error", url, "-o", str(partial)], check=True)
        partial.rename(archive)
    if digest(archive) != expected:
        raise RuntimeError("Toolchain archive checksum differs: " + name)
    binary = TOOLS / name.removesuffix(".tar.zst") / "bin/lean" if name.startswith("lean-") else destination / "bin/go"
    if not binary.exists():
        destination.mkdir(parents=True, exist_ok=True)
        cmd = ["tar", "--zstd" if name.endswith(".zst") else "-z", "-xf", str(archive), "-C", str(destination)]
        if strip:
            cmd.append("--strip-components=1")
        subprocess.run(cmd, check=True)
    print(name + ": pinned checksum verified", flush=True)
    return {"file": name, "url": url, "sha256": expected}

if __name__ == "__main__":
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        raise SystemExit("This bootstrap supports Linux x86-64 only")
    DOWNLOADS.mkdir(parents=True, exist_ok=True)
    with ThreadPoolExecutor(max_workers=3) as pool:
        records = list(pool.map(install, RELEASES))
    (TOOLS / "toolchains.json").write_text(json.dumps(records, indent=2) + "\n")
