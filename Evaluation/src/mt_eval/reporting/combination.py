import json
import os
from itertools import combinations
from src.config import (
    RESULTS_DIR
)

def main():
    if not os.path.exists(RESULTS_DIR):
        print(f"Directory '{RESULTS_DIR}' not found. Please ensure you are running this from the correct root folder.")
        return

    folder_names = sorted([
        d for d in os.listdir(RESULTS_DIR) 
        if os.path.isdir(os.path.join(RESULTS_DIR, d)) and d.startswith('results_')
    ])
    
    if not folder_names:
        print(f"No folders starting with 'results_' found in the '{RESULTS_DIR}' directory.")
        return

    strategies = [folder.replace('results_', '', 1) for folder in folder_names]
    
    unsupported_by_strategy = {strategy: set() for strategy in strategies}
    supported_mutants_by_strategy = {strategy: set() for strategy in strategies}
    
    total_programs = 0
    all_mutants = set()

    for folder_name in folder_names:
        print(f"\n" + "="*55)
        print(f"Analyzing Folder: {folder_name}")
        print("="*55)

        filename = os.path.join(RESULTS_DIR, folder_name, f"{folder_name}_rep_10.json")

        if not os.path.exists(filename):
            print(f"  -> File '{filename}' not found. Skipping...")
            continue

        with open(filename, 'r') as f:
            try:
                data = json.load(f)
            except json.JSONDecodeError:
                print(f"  -> Error parsing JSON in '{filename}'. Skipping...")
                continue

        strategy_name = folder_name.replace('results_', '', 1)

        stats = data.get("stats", {})
        if "total_programs" in stats:
            total_programs = stats["total_programs"]
        
        not_supported_list = data.get("not_supported", [])
        for item in not_supported_list:
            if isinstance(item, dict) and "program" in item:
                unsupported_by_strategy[strategy_name].add(item["program"])
        
        results_list = data.get("results", [])
        for result in results_list:
            if isinstance(result, dict) and "mutant_name" in result:
                mutant = result["mutant_name"]
                supported_mutants_by_strategy[strategy_name].add(mutant)
                all_mutants.add(mutant)

        print(f"  -> Processed {strategy_name}:")
        print(f"     - Unsupported programs: {len(unsupported_by_strategy[strategy_name])}")
        print(f"     - Evaluated mutants: {len(supported_mutants_by_strategy[strategy_name])}")

    print("\n" + "="*75)
    print("SUPPORTED PROGRAMS & MUTANTS ANALYSIS")
    print("="*75)
    print(f"Total Programs Evaluated: {total_programs}")
    print(f"Total Unique Mutants Found across all runs: {len(all_mutants)}\n")

    if total_programs == 0:
        print("Error: Could not find 'total_programs' in the JSON files.")
        return

    all_unsupported_programs = set()
    for s in strategies:
        all_unsupported_programs.update(unsupported_by_strategy[s])
        
    supported_programs_by_all = total_programs - len(all_unsupported_programs)
    supported_mutants_by_all = set.intersection(*[supported_mutants_by_strategy[s] for s in strategies]) if strategies else set()
    
    print(f"Supported by ALL {len(strategies)} strategies:")
    print(f"  - Programs: {supported_programs_by_all}")
    print(f"  - Mutants:  {len(supported_mutants_by_all)}\n")

    print("Supported by specific combinations (Programs | Mutants):")
    
    for r in range(1, len(strategies) + 1):
        for combo in combinations(strategies, r):
            combo_unsupported_programs = set()
            for s in combo:
                combo_unsupported_programs.update(unsupported_by_strategy[s])
            combo_supported_programs = total_programs - len(combo_unsupported_programs)
            
            combo_supported_mutants = set.intersection(*[supported_mutants_by_strategy[s] for s in combo])
            
            combo_name = " + ".join(combo)
            print(f"  - {combo_name:<35}: {combo_supported_programs:>3} programs | {len(combo_supported_mutants):>5} mutants")

if __name__ == "__main__":
    main()