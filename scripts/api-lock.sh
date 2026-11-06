#!/usr/bin/env bash
# Prints the public API of Inkproof.Scale, one line per declaration; CI compares it with API.lock.
# The generator is Inkproof.Core's api-lock executable. Regenerate with: scripts/api-lock.sh > API.lock
set -euo pipefail
cd "$(dirname "$0")/.."
lake build InkproofScale >&2
lake exe api-lock Inkproof.Scale Inkproof.Scale.Proofs
