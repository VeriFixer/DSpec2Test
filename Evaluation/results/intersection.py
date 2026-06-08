import json
import os
from itertools import combinations

def main():
    folders = sorted([d for d in os.listdir('.') if os.path.isdir(d) and d.startswith('results_')])
    
    if not folders:
        print("No folders starting with 'results_' found in the current directory.")
        return

    strategies = ["Block", "Path", "Spec", "Spec_bva"]
    
    # Dictionary to store the set of unsupported program names for each strategy
    unsupported_by_strategy = {strategy: set() for strategy in strategies}

    total_programs = 0

    for folder in folders:
        print(f"\n" + "="*55)
        print(f"Analyzing Folder: {folder}")
        print("="*55)

        # Assuming the json file is inside the folder. 
        # Adjust if the file is in the root directory.
        filename = os.path.join(folder, f"{folder}_rep_10.json")

        with open(filename, 'r') as f:
            try:
                data = json.load(f)
            except json.JSONDecodeError:
                print(f"  -> Error parsing JSON in '{filename}'. Skipping...")
                continue

        # Extract the necessary data
        strategy_name = data.get("strategy")
        stats = data.get("stats", {})
        
        # Capture the total number of programs (assuming it's identical across all strategies)
        if "total_programs" in stats:
            total_programs = stats["total_programs"]
        
        # Extract the names of the unsupported programs
        not_supported_list = data.get("not_supported", [])
        
        # Fallback to inferring strategy from folder name if the JSON 'strategy' key is missing/different
        if strategy_name not in strategies:
            for s in strategies:
                if s in folder:
                    strategy_name = s
                    break

        if strategy_name in unsupported_by_strategy:
            for item in not_supported_list:
                # Ensure the item is a dictionary and has the 'program' key
                if isinstance(item, dict) and "program" in item:
                    unsupported_by_strategy[strategy_name].add(item["program"])
            print(f"  -> Processed {strategy_name}: Found {len(unsupported_by_strategy[strategy_name])} unsupported programs.")
        else:
             print(f"  -> Unknown strategy '{strategy_name}' in '{filename}'.")

    # --- COMBINATION ANALYSIS ---
    print("\n" + "="*55)
    print("SUPPORTED PROGRAMS ANALYSIS")
    print("="*55)
    print(f"Total Programs Evaluated: {total_programs}\n")

    if total_programs == 0:
        print("Error: Could not find 'total_programs' in the JSON files.")
        return

    # 1. Supported by ALL strategies simultaneously
    # Intersection of Supported = Total - Union of Unsupported
    all_unsupported = set()
    for s in strategies:
        all_unsupported.update(unsupported_by_strategy[s])
        
    supported_by_all = total_programs - len(all_unsupported)
    print(f"Programs supported by ALL {len(strategies)} strategies: {supported_by_all}\n")

    # 2. Supported by ALL COMBINATIONS of strategies
    print("Programs supported by specific combinations:")
    
    # Generate combinations from single strategies up to all 4 strategies
    for r in range(1, len(strategies) + 1):
        for combo in combinations(strategies, r):
            combo_unsupported = set()
            for s in combo:
                combo_unsupported.update(unsupported_by_strategy[s])
            
            combo_supported = total_programs - len(combo_unsupported)
            combo_name = " + ".join(combo)
            print(f"  - {combo_name}: {combo_supported}")

if __name__ == "__main__":
    main()