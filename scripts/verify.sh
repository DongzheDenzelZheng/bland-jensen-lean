#!/usr/bin/env bash
set -euo pipefail

script_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
project_dir="$(CDPATH= cd -- "$script_dir/.." && pwd)"
cd "$project_dir"

if grep -R -n -E '(^|[^[:alnum:]_])(sorry|admit|native_decide|implemented_by)([^[:alnum:]_]|$)' \
    --include='*.lean' BlandJensenFormal; then
  printf '%s\n' 'Release gate failed: forbidden proof mechanism found.' >&2
  exit 1
fi

if grep -R -n -E '^[[:space:]]*(axiom|unsafe)[[:space:]]' \
    --include='*.lean' BlandJensenFormal; then
  printf '%s\n' 'Release gate failed: source-level axiom or unsafe declaration found.' >&2
  exit 1
fi

lake build BlandJensenFormal.Main
lake env lean Audit/KernelAxiomGate.lean

printf '%s\n' 'Release verification completed successfully.'
