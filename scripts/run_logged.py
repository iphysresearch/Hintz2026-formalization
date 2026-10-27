#!/usr/bin/env python3
"""Run a command and record its output and exit status.

Usage: python3 -I scripts/run_logged.py LOG COMMAND [ARGS ...]
"""

import datetime
import os
from pathlib import Path
import resource
import subprocess
import sys
import time


def now() -> str:
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


if len(sys.argv) < 3:
    raise SystemExit("usage: run_logged.py LOG COMMAND [ARGS ...]")
log_path, *command = sys.argv[1:]
Path(log_path).parent.mkdir(parents=True, exist_ok=True)

with open(log_path, "w", encoding="utf-8") as log:
    log.write(f"cwd={os.getcwd()}\ncmd={' '.join(command)}\nstart={now()}\n")
    log.flush()
    started = time.time()
    result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT)
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    log.write(
        f"\nexit={result.returncode} wall_secs={time.time() - started:.1f} "
        f"peak_child_rss_MB={usage.ru_maxrss / 1024:.0f} end={now()}\n"
    )

raise SystemExit(result.returncode)
