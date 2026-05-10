#!/usr/bin/env python3
"""
Applies manual override classifications from manually_analysis.json to the
raw results (Block and Spec_bva) and prints the corrected results table.

Output: Table 1 — Mutation kill rates and kill overlap on the 131
realistically-killable mutants. Timeouts (TO) are runtime infinite loops
introduced by the mutation and credited as kills.
"""

import json
import os

RESULTS_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")


def load_json(filename):
    with open(os.path.join(RESULTS_DIR, filename)) as f:
        return json.load(f)


def main():
    block = load_json("results_DafnyTestGenerator_Block.json")
    spec_bva = load_json("results_DafnyTestGenerator_Spec_bva.json")
    manual = load_json("manually_analysis.json")

    # Index manual results by mutant_name
    manual_map = {r["mutant_name"]: r for r in manual["results"]}

    # Filter to realistically-killable only
    rk = [
        r for r in manual["results"]
        if r["manual_classification"] in ("killed", "killed_timeout", "survived")
    ]

    # Per-tool raw counts on the 131
    block_fail = sum(1 for r in rk if r["original_block_status"] == "killed")
    block_to = sum(1 for r in rk if r["original_block_status"] == "timeout")
    block_killed = sum(1 for r in rk if r["corrected_block_status"] == "killed")
    block_surv = sum(1 for r in rk if r["corrected_block_status"] == "survived")

    spec_fail = sum(1 for r in rk if r["original_spec_bva_status"] == "killed")
    spec_to = sum(1 for r in rk if r["original_spec_bva_status"] == "timeout")
    spec_killed = sum(1 for r in rk if r["corrected_spec_bva_status"] == "killed")
    spec_surv = sum(1 for r in rk if r["corrected_spec_bva_status"] == "survived")

    # Overlap
    both = sum(
        1 for r in rk
        if r["corrected_block_status"] == "killed"
        and r["corrected_spec_bva_status"] == "killed"
    )
    block_only = sum(
        1 for r in rk
        if r["corrected_block_status"] == "killed"
        and r["corrected_spec_bva_status"] == "survived"
    )
    spec_only = sum(
        1 for r in rk
        if r["corrected_block_status"] == "survived"
        and r["corrected_spec_bva_status"] == "killed"
    )
    neither = sum(
        1 for r in rk
        if r["corrected_block_status"] == "survived"
        and r["corrected_spec_bva_status"] == "survived"
    )
    union = both + block_only + spec_only

    n = len(rk)

    # Print table
    print("=" * 72)
    print("Table 1: Mutation kill rates (top) and kill overlap (bottom)")
    print("on the 131 realistically-killable mutants.")
    print("Timeouts (TO) are runtime infinite loops introduced by the mutation")
    print("and credited as kills. The Killed column is FAIL + TO.")
    print("=" * 72)
    print()
    hdr = f"{'Strategy':<22} {'FAIL':>5} {'TO':>5} {'Killed':>7} {'Surv.':>6} {'Kill%':>7}"
    print(hdr)
    print("-" * len(hdr))
    print(
        f"{'Block (WB)':<22} {block_fail:>5} {block_to:>5} {block_killed:>7} "
        f"{block_surv:>6} {block_killed/n*100:>6.1f}%"
    )
    print(
        f"{'Spec_bva (BB)':<22} {spec_fail:>5} {spec_to:>5} {spec_killed:>7} "
        f"{spec_surv:>6} {spec_killed/n*100:>6.1f}%"
    )
    print(
        f"{'Union':<22} {'—':>5} {'—':>5} {union:>7} "
        f"{neither:>6} {union/n*100:>6.1f}%"
    )
    print()
    print(f"{'Killed by both':<22} {'—':>5} {'—':>5} {both:>7} {'—':>6} {both/n*100:>6.1f}%")
    print(f"{'Killed by Block only':<22} {'—':>5} {'—':>5} {block_only:>7} {'—':>6} {block_only/n*100:>6.1f}%")
    print(f"{'Killed by Spec_bva only':<22} {'—':>5} {'—':>5} {spec_only:>7} {'—':>6} {spec_only/n*100:>6.1f}%")
    print(f"{'Killed by neither':<22} {'—':>5} {'—':>5} {neither:>7} {'—':>6} {neither/n*100:>6.1f}%")
    print()
    print(f"Denominator (realistically-killable): {n}")
    print(f"Excluded: {manual['stats']['incompetent']} incompetent + "
          f"{manual['stats']['equivalent']} equivalent = "
          f"{manual['stats']['incompetent'] + manual['stats']['equivalent']} "
          f"(from 170 common mutants)")


if __name__ == "__main__":
    main()
