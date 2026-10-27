#!/usr/bin/env bash
set -euo pipefail

export -n LD_LIBRARY_PATH 2>/dev/null || true
export -n LD_PRELOAD 2>/dev/null || true
export -n CONDA_PREFIX 2>/dev/null || true
export -n CONDA_DEFAULT_ENV 2>/dev/null || true
export PATH="$HOME/.elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"

cd "$(dirname "$0")/.."
echo "=== Hintz2026 isolated Lean build ==="
lean --version
exec "$@"
