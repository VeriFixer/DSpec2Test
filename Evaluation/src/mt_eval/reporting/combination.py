import os
import json
import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns

# ==========================================
# Configuration
# ==========================================
sns.set_theme(style="whitegrid", context="paper")
COLORS = {"Block": "#1f77b4", "Spec_bva": "#d62728", "Combined": "#2ca02c"}
MARKERS = {"Block": "o", "Spec_bva": "D", "Combined": "*"}

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
    
    for x in range(1, max_x + 1):
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
    print(f"HEHEEH: {len(shared_programs)}")
    return shared_programs

def evaluate_combination(base_dir, valid_programs, strat_a, strat_b, max_x):
    """Evaluates individual and combined kill rates across X."""
    records = []
    
    for x in range(1, max_x + 1):
        path_a = os.path.join(base_dir, f"results_{strat_a}", f"results_{strat_a}_rep_{x}.json")
        path_b = os.path.join(base_dir, f"results_{strat_b}", f"results_{strat_b}_rep_{x}.json")
        
        if not os.path.exists(path_a) or not os.path.exists(path_b):
            continue
            
        with open(path_a, 'r') as fa, open(path_b, 'r') as fb:
            data_a = json.load(fa)
            data_b = json.load(fb)
            
        # Dictionaries to hold mutant statuses: {mutant_name: status}
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
                
        # All unique mutants identified across valid programs
        all_mutants = set(mutants_a.keys()).union(set(mutants_b.keys()))
        total_mutants = len(all_mutants)
        
        if total_mutants == 0:
            continue
            
        kills_a = 0
        kills_b = 0
        kills_combined = 0
        
        kill_indicators = {"killed", "timeout"}
        
        # Calculate overlapping and unique kills
        for m in all_mutants:
            status_a = mutants_a.get(m, "error")
            status_b = mutants_b.get(m, "error")
            
            is_killed_a = status_a in kill_indicators
            is_killed_b = status_b in kill_indicators
            
            if is_killed_a: kills_a += 1
            if is_killed_b: kills_b += 1
            if is_killed_a or is_killed_b: kills_combined += 1
            
        # Append separated records for clean plotting
        base_record = {"X": x, "Total Mutants": total_mutants}
        
        records.append({**base_record, "Strategy": strat_a, "Killed": kills_a, "Kill Rate": kills_a / total_mutants})
        records.append({**base_record, "Strategy": strat_b, "Killed": kills_b, "Kill Rate": kills_b / total_mutants})
        records.append({**base_record, "Strategy": "Combined", "Killed": kills_combined, "Kill Rate": kills_combined / total_mutants})

    return pd.DataFrame(records)

def plot_combination(df, out_dir):
    max_x = int(df["X"].max())
    plt.figure(figsize=(7, 5))
    
    ax = sns.lineplot(
        data=df, x="X", y="Kill Rate", hue="Strategy", style="Strategy",
        palette=COLORS, markers=MARKERS, dashes=False, linewidth=2.5, markersize=9
    )
    
    plt.title("Synergy Check: Individual vs Combined Kill Rate")
    plt.xlabel("Repeat Factor (X)")
    plt.ylabel("Kill Rate")
    plt.xticks(range(1, max_x + 1))
    
    vals = ax.get_yticks()
    ax.set_yticks(vals)
    ax.set_yticklabels(['{:,.1%}'.format(x) for x in vals])
    
    plt.legend(title="Strategy")
    plt.savefig(os.path.join(out_dir, "plot_10_combined_synergy.png"), bbox_inches='tight')
    plt.close()

if __name__ == "__main__":
    output_dir = "results"
    graphs_dir = os.path.join(output_dir, "graphs")
    os.makedirs(graphs_dir, exist_ok=True)
    
    max_x = get_max_repetition(output_dir)
    print(f"Detected Max X = {max_x}")
    
    all_strategies = ["Block", "Path", "Spec", "Spec_bva"]
    strat_a = "Block"
    strat_b = "Spec_bva"
    
    # 1. Get programs supported by EVERY strategy
    valid_programs = get_globally_shared_programs(output_dir, all_strategies, max_x)
    print(f"Found {len(valid_programs)} globally supported programs.")
    
    if len(valid_programs) > 0:
        # 2. Evaluate
        df_combo = evaluate_combination(output_dir, valid_programs, strat_a, strat_b, max_x)
        
        # 3. Save Table
        table_path = os.path.join(output_dir, "tables", "table_7_combination_synergy.csv")
        os.makedirs(os.path.dirname(table_path), exist_ok=True)
        # Pivot for easy reading
        df_pivot = df_combo.pivot(index="X", columns="Strategy", values="Kill Rate")
        df_pivot = (df_pivot * 100).round(2)
        df_pivot.to_csv(table_path)
        print(f"\nSynergy Table saved to {table_path}")
        print(df_pivot)
        
        # 4. Plot
        plot_combination(df_combo, graphs_dir)
        print(f"Synergy Graph saved to {graphs_dir}/plot_10_combined_synergy.png")