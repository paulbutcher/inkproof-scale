#!/usr/bin/env bash
# Prints the public API of Inkproof.Scale, one line per declaration; CI compares it with API.lock.
# The generator is Inkproof.Core's api-lock executable. Regenerate with: scripts/api-lock.sh > API.lock
set -euo pipefail
cd "$(dirname "$0")/.."
lake build InkproofScale inkproof-core/api-lock >&2

# Lean resolves a module by its first path component, so with Inkproof.Core and Inkproof.Scale in
# different build directories the generator would look for both in one. Merge their `Inkproof`
# directories with links.
merged="$(mktemp -d)"
trap 'rm -rf "$merged"' EXIT
mkdir "$merged/Inkproof"
IFS=: read -ra dirs <<< "$(lake env printenv LEAN_PATH)"
for d in "${dirs[@]}"; do
  [ -d "$d/Inkproof" ] || continue
  for e in "$d/Inkproof"/*; do
    ln -sfn "$e" "$merged/Inkproof/$(basename "$e")"
  done
done
LEAN_PATH="$merged:$(IFS=:; echo "${dirs[*]}")" \
  "$(lake query inkproof-core/api-lock 2>/dev/null)" Inkproof.Scale Inkproof.Scale.Proofs
