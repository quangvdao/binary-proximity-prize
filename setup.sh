#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export LAKE_ARTIFACT_CACHE=false
export LAKE_NO_CACHE=true
if [[ "${1:-}" == --verifier && $# == 1 ]]; then
  exec bash scripts/setup-verifier.sh
fi
[[ $# == 0 ]] || { echo 'usage: ./setup.sh [--verifier]' >&2; exit 2; }
command -v lake >/dev/null || { echo 'Install elan/Lean before running setup.' >&2; exit 1; }
lake exe cache get
lake build
lake env lean scripts/check-axioms.lean
python3 scripts/check-initial-bounds.py
printf '%s\n' 'Binary challenge build and initial-bound checks passed.'
