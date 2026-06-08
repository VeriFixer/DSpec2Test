import json
import os

def get_killed_mutants(filepath):
    """Parses a JSON file and returns a set of mutant_names that were 'killed'."""
    if not os.path.exists(filepath):
        return set()
    
    with open(filepath, 'r') as f:
        try:
            data = json.load(f)
            # Extract mutant names where the status is exactly "killed"
            return {
                mutant['mutant_name'] 
                for mutant in data.get('results', []) 
                if mutant.get('status') == 'killed'
            }
        except json.JSONDecodeError:
            print(f"  [!] Error reading JSON from {filepath}")
            return set()

def main():
    # Automatically find all folders starting with 'results_'
    folders = sorted([d for d in os.listdir('.') if os.path.isdir(d) and d.startswith('results_')])
    
    if not folders:
        print("No folders starting with 'results_' found in the current directory.")
        return

    # Added "Path" to the pipeline
    strategies = ["Block", "Path", "Spec", "Spec_bva"]
    
    # Aggregated stats across all folders
    total_all_folders = set()

    for folder in folders:
        print(f"\n" + "="*55)
        print(f"Analyzing Folder: {folder}")
        print("="*55)
        
        killed_sets = {}
        
        for strategy in strategies:
            filename = f"results_DafnyTestGenerator_{strategy}.json"
            filepath = os.path.join(folder, filename)
            killed_sets[strategy] = get_killed_mutants(filepath)
            
        block = killed_sets["Block"]
        path = killed_sets["Path"]
        spec = killed_sets["Spec"]
        spec_bva = killed_sets["Spec_bva"]
        
        # Calculate total unique across all 4 strategies
        total_unique = block | path | spec | spec_bva
        total_all_folders.update(total_unique)
        
        if not total_unique:
            print("  No mutants were killed by any strategy in this folder.")
            continue
        
        # OVERALL SUMMARY
        print(f"Total Unique Mutants Killed (All 4): {len(total_unique)}")
        print("-" * 55)
        print("Total Kills per Strategy:")
        print(f"  Block:           {len(block)}")
        print(f"  Path:            {len(path)}")
        print(f"  Spec:            {len(spec)}")
        print(f"  Spec_bva:        {len(spec_bva)}")
        print("-" * 55)
        
        # 1. STRUCTURAL MATCHUP
        print("ROUND 1: Structural Strategies (Block vs. Path)")
        structural_combined = block | path
        print(f"  Combined Kills:  {len(structural_combined)}")
        print(f"  Only Block:      {len(block - path)} (Missed by Path)")
        print(f"  Only Path:       {len(path - block)} (Missed by Block)")
        print(f"  Both:            {len(block & path)}")
        print("-" * 55)

        # 2. SPECIFICATION MATCHUP
        print("ROUND 2: Specification Strategies (Spec vs. Spec_bva)")
        spec_combined = spec | spec_bva
        print(f"  Combined Kills:  {len(spec_combined)}")
        print(f"  Only Spec:       {len(spec - spec_bva)} (Missed by Spec_bva)")
        print(f"  Only Spec_bva:   {len(spec_bva - spec)} (Missed by Spec)")
        print(f"  Both:            {len(spec & spec_bva)}")
        print("-" * 55)
        
        # 3. CATEGORY MATCHUP (To answer your final goal)
        print("FINAL EVALUATION: Structural vs. Specification")
        print("  (Comparing the combined structural net vs combined spec net)")
        print(f"  Exclusively Structural:  {len(structural_combined - spec_combined)}")
        print(f"  Exclusively Spec:        {len(spec_combined - structural_combined)}")
        print(f"  Killed by BOTH logic:    {len(structural_combined & spec_combined)}")

if __name__ == "__main__":
    main()