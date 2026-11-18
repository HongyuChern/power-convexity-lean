#!/usr/bin/env bash
set -euo pipefail
: "${POWER_COMPARATOR:?Set the absolute path to the pinned Comparator executable}"
: "${COMPARATOR_LEAN4EXPORT:?Set the absolute path to the pinned lean4export executable}"
: "${COMPARATOR_LANDRUN:?Set the absolute path to the Linux landrun executable}"
: "${COMPARATOR_NANODA:?Set the absolute path to nanoda_bin}"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
if [[ -z ${TMPDIR:-} ]]; then
    TMPDIR="$(mktemp -d)"
fi
export TMPDIR
systemd-run --user --wait --pipe --collect \
  --property=RestrictAddressFamilies=~AF_UNIX --working-directory="$PWD" \
  --setenv="PATH=$PATH" --setenv="TMPDIR=$TMPDIR" --setenv="LEAN_NUM_THREADS=$LEAN_NUM_THREADS" \
  --setenv="COMPARATOR_LEAN4EXPORT=$COMPARATOR_LEAN4EXPORT" \
  --setenv="COMPARATOR_LANDRUN=$COMPARATOR_LANDRUN" --setenv="COMPARATOR_NANODA=$COMPARATOR_NANODA" \
  lake env "$POWER_COMPARATOR" PowerConvexityComparator/config.json
