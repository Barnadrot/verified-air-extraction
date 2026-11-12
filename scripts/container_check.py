"""Measure the documented bootstrap and full build in a fresh container."""
from pathlib import Path
import datetime
import json
import os
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / "proofs/divrem/artifacts"


def cgroup(name):
    path = Path("/sys/fs/cgroup") / name
    return path.read_text().strip() if path.exists() else None


def main():
    LOG.mkdir(parents=True, exist_ok=True)
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    begin = time.monotonic()
    result = subprocess.run(
        ["/usr/bin/time", "-v", "-o", str(LOG / "clean-environment-time.log"),
         "bash", "-lc", "python3 bootstrap.py && bash build.sh --clean"], cwd=ROOT)
    record = {
        "status": "passed" if result.returncode == 0 else "failed",
        "exit_code": result.returncode,
        "started_utc": started,
        "completed_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "wall_seconds_including_bootstrap": round(time.monotonic() - begin, 2),
        "fresh_environment": "container image excludes work/, .lake/, artifacts/ and local Perennial checkout",
        "logical_cpus_visible": os.cpu_count(),
        "cpu_quota": cgroup("cpu.max"),
        "memory_limit_bytes": cgroup("memory.max"),
        "memory_peak_bytes": cgroup("memory.peak"),
        "swap_limit_bytes": cgroup("memory.swap.max"),
        "swap_peak_bytes": cgroup("memory.swap.peak"),
        "measurement": "cgroup peak is aggregate container memory; GNU time reports largest individual child RSS",
    }
    (LOG / "clean-environment-resources.json").write_text(json.dumps(record, indent=2) + "\n")
    raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
