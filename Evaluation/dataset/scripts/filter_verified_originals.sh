#!/bin/bash
# filter_verified_originals.sh — Parallel dafny verify filter for .dfy files
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$("$SCRIPT_DIR/find_repo_root.sh")"

usage() {
    echo "Usage: $0 <input_dir> <output_dir> [max_jobs]" >&2
    echo "  input_dir   Directory containing .dfy files to verify" >&2
    echo "  output_dir  Directory to copy verified files into" >&2
    echo "  max_jobs    Max parallel jobs (default: nproc - 1, min 1)" >&2
    exit 1
}

if [ $# -lt 2 ]; then
    usage
fi

INPUT_DIR="$1"
OUTPUT_DIR="$2"
NPROC="$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 2)"
DEFAULT_JOBS=$(( NPROC > 1 ? NPROC - 1 : 1 ))
MAX_JOBS="${3:-$DEFAULT_JOBS}"

DAFNY="${DAFNY:-dafny}"

if [ ! -d "$INPUT_DIR" ]; then
    echo "ERROR: Input directory '$INPUT_DIR' does not exist." >&2
    exit 1
fi

mkdir -p "$OUTPUT_DIR"

# Collect .dfy files
mapfile -t DFY_FILES < <(find "$INPUT_DIR" -name '*.dfy' -type f | sort)
TOTAL=${#DFY_FILES[@]}

if [ "$TOTAL" -eq 0 ]; then
    echo "WARNING: No .dfy files found in '$INPUT_DIR'." >&2
    exit 0
fi

echo "Verifying $TOTAL files with up to $MAX_JOBS parallel jobs..."

PASS_COUNT=0
FAIL_COUNT=0

# Temp dir for result tracking
RESULTS_DIR="$(mktemp -d)"
trap 'rm -rf "$RESULTS_DIR"' EXIT

verify_one() {
    local f="$1"
    local basename
    basename="$(basename "$f")"
    if $DAFNY verify --allow-warnings "$f" >/dev/null 2>&1; then
        cp "$f" "$OUTPUT_DIR/$basename"
        echo "pass" > "$RESULTS_DIR/$basename.result"
    else
        echo "fail" > "$RESULTS_DIR/$basename.result"
    fi
}

export -f verify_one
export DAFNY OUTPUT_DIR RESULTS_DIR

# Use GNU parallel if available, else fall back to xargs
if command -v parallel >/dev/null 2>&1; then
    printf '%s\n' "${DFY_FILES[@]}" | parallel -j "$MAX_JOBS" verify_one {}
else
    printf '%s\n' "${DFY_FILES[@]}" | xargs -P "$MAX_JOBS" -I {} bash -c 'verify_one "$@"' _ {}
fi

# Count results
for f in "${DFY_FILES[@]}"; do
    BASENAME="$(basename "$f")"
    RESULT_FILE="$RESULTS_DIR/$BASENAME.result"
    if [ -f "$RESULT_FILE" ] && [ "$(cat "$RESULT_FILE")" = "pass" ]; then
        PASS_COUNT=$((PASS_COUNT + 1))
    else
        FAIL_COUNT=$((FAIL_COUNT + 1))
    fi
done

echo "Verification complete: $PASS_COUNT passed, $FAIL_COUNT failed (total: $TOTAL)"
