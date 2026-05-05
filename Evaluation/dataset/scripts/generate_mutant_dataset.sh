#!/bin/bash
# generate_mutant_dataset.sh — Invoke MutDafny on .dfy files with progress reporting
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$("$SCRIPT_DIR/find_repo_root.sh")"

usage() {
    echo "Usage: $0 <input_dir> <output_dir>" >&2
    echo "  input_dir   Directory containing .dfy files to mutate" >&2
    echo "  output_dir  Directory to write mutant .dfy files" >&2
    exit 1
}

if [ $# -lt 2 ]; then
    usage
fi

INPUT_DIR="$1"
OUTPUT_DIR="$2"

if [ ! -d "$INPUT_DIR" ]; then
    echo "ERROR: Input directory '$INPUT_DIR' does not exist." >&2
    exit 1
fi

# Resolve MutDafny path
MUTDAFNY="${MUTDAFNY:-$REPO_ROOT/external/mutation/mutdafny/Binaries/MutDafny}"

if [ ! -f "$MUTDAFNY" ]; then
    echo "WARNING: MutDafny binary not found at '$MUTDAFNY'. Set MUTDAFNY env var." >&2
fi

mkdir -p "$OUTPUT_DIR"

# Collect .dfy files
mapfile -t DFY_FILES < <(find "$INPUT_DIR" -name '*.dfy' -type f | sort)
TOTAL=${#DFY_FILES[@]}

if [ "$TOTAL" -eq 0 ]; then
    echo "WARNING: No .dfy files found in '$INPUT_DIR'." >&2
    exit 0
fi

echo "Generating mutants for $TOTAL files..."

CURRENT=0
FAILURES=0
for f in "${DFY_FILES[@]}"; do
    CURRENT=$((CURRENT + 1))
    BASENAME="$(basename "$f")"
    echo "[$CURRENT/$TOTAL] Mutating: $BASENAME"

    if ! "$MUTDAFNY" "$f" "$OUTPUT_DIR" 2>/dev/null; then
        echo "  WARNING: MutDafny failed on '$BASENAME', skipping." >&2
        FAILURES=$((FAILURES + 1))
        continue
    fi
done

echo "Done. Processed $TOTAL files, $FAILURES failures."
