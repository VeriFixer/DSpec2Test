#!/bin/bash
# find_repo_root.sh — Walk up from current dir looking for .repo_mutation_testing_marker
set -euo pipefail

MARKER=".repo_mutation_testing_marker"

find_root() {
    local dir
    dir="$(pwd)"
    while [ "$dir" != "/" ]; do
        if [ -f "$dir/$MARKER" ]; then
            echo "$dir"
            return 0
        fi
        dir="$(dirname "$dir")"
    done
    # Check root as well
    if [ -f "/$MARKER" ]; then
        echo "/"
        return 0
    fi
    echo "ERROR: Marker file '$MARKER' not found in any parent directory." >&2
    return 1
}

find_root
