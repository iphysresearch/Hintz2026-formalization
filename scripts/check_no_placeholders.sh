#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
command -v rg >/dev/null
if rg -n --glob '*.lean' 'sorry|admit|native_decide|Lean\.ofReduceBool' Hintz2026.lean Hintz2026 audit; then
  echo "forbidden proof placeholder found" >&2
  exit 1
fi
echo "no forbidden proof placeholders found"
