import os
import argparse
import json
import pandas as pd
from src.config import (
    RESULTS_DIR
)

def get_max_repetition(base_dir):
    """Dynamically detects the maximum X by scanning the folder structure."""
    max_x = 0
    for item in os.listdir(base_dir):
        if item.startswith("results_") and os.path.isdir(os.path.join(base_dir, item)):
            strat_dir = os.path.join(base_dir, item)
            for file in os.listdir(strat_dir):
                if file.endswith(".json") and "_rep_" in file:
                    try:
                        x_val = int(file.split("_rep_")[-1].replace(".json", ""))
                        max_x = max(max_x, x_val)
                    except ValueError:
                        pass
    return max_x

def get_globally_shared_programs(base_dir, all_strategies, target_x):
    """Finds programs supported by ALL specified strategies to ensure a fair baseline."""
    all_encountered = set()
    unsupported_in_combo = set()
    
    for x in range(1, target_x + 1):
        for strategy in all_strategies:
            strat_path = os.path.join(base_dir, f"results_{strategy}", f"results_{strategy}_rep_{x}.json")
            
            if os.path.exists(strat_path):
                with open(strat_path, 'r') as sf:
                    data = json.load(sf)
                
                timing_data = data.get("timing", {}).get("per_program", {})
                for prog in timing_data.keys():
                    all_encountered.add(prog.replace(".dfy", ""))
                
                not_supported_list = data.get("not_supported", [])
                for item in not_supported_list:
                    if isinstance(item, dict) and "program" in item:
                        unsupported_in_combo.add(item["program"].replace(".dfy", ""))
            
    shared_programs = all_encountered - unsupported_in_combo
    return shared_programs

def evaluate_combination(base_dir, valid_programs, strat_a, strat_b, max_x):
    """Evaluates individual and combined kill rates across Reps."""
    records = []
    
    for x in range(1, max_x + 1):
        path_a = os.path.join(base_dir, f"results_{strat_a}", f"results_{strat_a}_rep_{x}.json")
        path_b = os.path.join(base_dir, f"results_{strat_b}", f"results_{strat_b}_rep_{x}.json")
        
        if not os.path.exists(path_a) or not os.path.exists(path_b):
            continue
            
        with open(path_a, 'r') as fa, open(path_b, 'r') as fb:
            data_a = json.load(fa)
            data_b = json.load(fb)
            
        mutants_a = {}
        mutants_b = {}
        
        for res in data_a.get("results", []):
            prog = res.get("original_name", "").replace(".dfy", "")
            if prog in valid_programs:
                mutants_a[res.get("mutant_name")] = res.get("status", "")
                
        for res in data_b.get("results", []):
            prog = res.get("original_name", "").replace(".dfy", "")
            if prog in valid_programs:
                mutants_b[res.get("mutant_name")] = res.get("status", "")
                
        all_mutants = set(mutants_a.keys()).union(set(mutants_b.keys()))
        total_mutants = len(all_mutants)
        
        if total_mutants == 0:
            continue
            
        kills_a = 0
        kills_b = 0
        kills_combined = 0
        
        kill_indicators = {"killed", "timeout"}
        
        for m in all_mutants:
            status_a = mutants_a.get(m, "error")
            status_b = mutants_b.get(m, "error")
            
            is_killed_a = status_a in kill_indicators
            is_killed_b = status_b in kill_indicators
            
            if is_killed_a: kills_a += 1
            if is_killed_b: kills_b += 1
            if is_killed_a or is_killed_b: kills_combined += 1
            
        base_record = {"Rep": x, "Total Mutants": total_mutants}
        
        records.append({**base_record, "Strategy": strat_a, "Killed": kills_a, "Kill Rate": kills_a / total_mutants})
        records.append({**base_record, "Strategy": strat_b, "Killed": kills_b, "Kill Rate": kills_b / total_mutants})
        records.append({**base_record, "Strategy": "Combined", "Killed": kills_combined, "Kill Rate": kills_combined / total_mutants})

    return pd.DataFrame(records)

def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    """Parse CLI arguments."""
    parser = argparse.ArgumentParser(
        description="Run mutation kill evaluation on selected programs."
    )
    parser.add_argument(
        "--strat-a",
        type=str,
        default="Path",
        help="First strategie to evaluate combination on",
    )
    parser.add_argument(
        "--strat-b",
        type=str,
        default="Spec_bva",
        help="Second strategie to evaluate combination on",
    )
    return parser.parse_args(argv)



def main(argv: list[str] | None = None) -> None:
    args = parse_args(argv)

    output_dir = RESULTS_DIR
    os.makedirs(output_dir, exist_ok=True)
    graphs_dir = os.path.join(output_dir, "graphs")
    os.makedirs(graphs_dir, exist_ok=True)
    
    max_x = get_max_repetition(output_dir)
    print(f"Detected Max Rep = {max_x}")
    
    all_strategies = ["Block", "Path", "Spec", "Spec_bva"]
    
    valid_programs = get_globally_shared_programs(output_dir, all_strategies, max_x)
    print(f"Found {len(valid_programs)} globally supported programs.")
    
    if len(valid_programs) > 0:
        df_combo = evaluate_combination(output_dir, valid_programs, args.strat_a, args.strat_b, max_x)
        
        table_path = os.path.join(output_dir, "tables", "table_0_combination.csv")
        os.makedirs(os.path.dirname(table_path), exist_ok=True)
        df_pivot = df_combo.pivot(index="Rep", columns="Strategy", values="Kill Rate")
        df_pivot = df_pivot[[args.strat_a, "Combined", args.strat_b]]
        df_pivot = (df_pivot * 100).round(2)
        df_pivot.to_csv(table_path)
        with open(os.path.join(output_dir, "tables", "table_0_combination.tex"), "w") as f:
            f.write(df_pivot.to_latex(float_format="%.2f", escape=True))
        print(f"\Combination Table saved to {table_path}")
        print(df_pivot)
        
if __name__ == "__main__":
    main()