"""Check publication paths, links and excluded build products. No proof claim."""
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    # Git's candidate set excludes dependency checkouts, generated artifacts and caches.
    raw = subprocess.check_output(["git", "ls-files", "-co", "--exclude-standard", "-z"], cwd=ROOT)
    names = sorted(set(n.decode() for n in raw.split(b"\0") if n))
    names = [n for n in names if (ROOT / n).is_file()]
    errors = []
    for name in names:
        path = ROOT / name
        if not path.is_file():
            continue
        if any(part in {".lake", "__pycache__", ".git"} for part in path.relative_to(ROOT).parts):
            errors.append("Build product in candidate files: " + name)
        if path.stat().st_size > 95 * 1024 * 1024:
            errors.append("File exceeds repository blob limit: " + name)
        content = path.read_text(encoding="utf-8-sig")
        machine_path = r"/" + r"home/[^/\s]+/|[A-Z]:[\\/]Users[\\/]|AppData[\\/]"
        if re.search(machine_path, content):
            errors.append("Machine-specific path: " + name)
        if path.suffix == ".md":
            for target in re.findall(r"\]\(([^)]+)\)", content):
                if "://" in target or target.startswith("#"):
                    continue
                if not (path.parent / target.split("#")[0]).exists():
                    errors.append(f"Broken link in {name}: {target}")
    if errors:
        raise SystemExit("\n".join(errors))
    total = sum((ROOT / n).stat().st_size for n in names)
    print(f"Repository checks passed: {len(names)} text files, {total:,} bytes")
    print("These are publication checks, not Lean verification.")


if __name__ == "__main__":
    main()
