import os
import json
import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns
import statistics

# ==========================================
# Configuration for Scientific Paper Style
# ==========================================
sns.set_theme(style="whitegrid", context="paper")
plt.rcParams.update({
    'font.size': 12,
    'axes.labelsize': 14,
    'axes.titlesize': 14,
    'legend.fontsize': 11,
    'xtick.labelsize': 11,
    'ytick.labelsize': 11,
    'figure.dpi': 300,
    'savefig.bbox': 'tight',
    'font.family': 'serif' # Often preferred for papers
})

# ==========================================
# Explicit Style Mappings for Consistency
# ==========================================
STRATEGY_COLORS = {
    "Block": "#1f77b4",     # Blue
    "Path": "#ff7f0e",      # Orange
    "Spec": "#2ca02c",      # Green
    "Spec_bva": "#d62728"   # Red
}

STRATEGY_MARKERS = {
    "Block": "o",           # Circle
    "Path": "s",            # Square
    "Spec": "^",            # Triangle up
    "Spec_bva": "D"         # Diamond
}

# ==========================================
# Data Processing
# ==========================================

def get_excluded_programs(base_dir):
    """
    Dynamically fetches the list of excluded programs from the X=7 Path strategy results.
    """
    path_file = os.path.join(base_dir, "results_7", "results_DafnyTestGenerator_Path.json")
    excluded = set()
    
    if os.path.exists(path_file):
        with open(path_file, 'r') as f:
            data = json.load(f)
            
        not_supported = data.get("not_supported", [])
        for item in not_supported:
            prog = item.get("program", "")
            if prog:
                # Strip .dfy to ensure clean matching
                excluded.add(prog.replace(".dfy", ""))
                
        print(f"Dynamically loaded {len(excluded)} excluded programs from X=7 Path strategy.")
    else:
        print(f"Warning: {path_file} not found. Proceeding with 0 excluded programs.")
        
    return excluded


def load_data(base_dir="results"):
    """
    Parses the folder structure and JSON files into two DataFrames:
    1. df_full: Data for strategies that support 100% of the programs.
    2. df_common: Data for all strategies, calculated on all programs EXCEPT the dynamically excluded ones.
    """
    records_full = []
    records_common = []
    
    # Dynamically fetch the list of programs to exclude
    excluded_programs = get_excluded_programs(base_dir)
    
    for x in range(1, 8):
        folder_path = os.path.join(base_dir, f"results_{x}")
        comp_path = os.path.join(folder_path, "comparison.json")
        
        if not os.path.exists(comp_path):
            print(f"Warning: {comp_path} not found. Skipping X={x}.")
            continue
            
        with open(comp_path, 'r') as f:
            comp_data = json.load(f)
            
        strategies_comp = comp_data.get("strategies", {})
        
        # 1. Identify which strategies support all programs
        fully_supported_strats = [
            strat for strat, stats in strategies_comp.items() 
            if stats.get("not_supported_programs", 0) == 0
        ]
        
        # 2. Load the individual strategy JSONs to analyze the program-level data
        strat_data_map = {}
        for strategy in strategies_comp.keys():
            strat_path = os.path.join(folder_path, f"results_{strategy}.json")
            if os.path.exists(strat_path):
                with open(strat_path, 'r') as sf:
                    strat_data_map[strategy] = json.load(sf)
                    
        # 3. Define the common programs by excluding the dynamically extracted problematic ones
        all_encountered_programs = set()
        for strat, data in strat_data_map.items():
            all_encountered_programs.update(data.get("timing", {}).get("per_program", {}).keys())
            
        # Strip '.dfy' from the encountered programs just in case, then filter
        all_encountered_programs = {p.replace(".dfy", "") for p in all_encountered_programs}
        common_programs = all_encountered_programs - excluded_programs

        # 4. Build the records
        for strategy, stats in strategies_comp.items():
            clean_name = strategy.replace("DafnyTestGenerator_", "")
            
            # --- DATASET A: FULLY SUPPORTED STRATEGIES ---
            if strategy in fully_supported_strats:
                total_time = 0
                if strategy in strat_data_map:
                    timing_data = strat_data_map[strategy].get("timing", {}).get("per_program", {})
                    for prog, times in timing_data.items():
                        total_time += times.get("test_gen_time", 0) + times.get("safety_check_time", 0)
                        
                records_full.append({
                    "X": x,
                    "Strategy": clean_name,
                    "Kill Rate": stats.get("kill_rate", 0),
                    "Killed": stats.get("killed", 0),
                    "Survived": stats.get("survived", 0),
                    "Timeout": stats.get("timeout", 0),
                    "Error": stats.get("error", 0),
                    "Total Number of Tests": stats.get("total_num_tests", 0),
                    "Average Number of Tests": stats.get("avg_num_tests", 0),
                    "Median Number of Tests": stats.get("median_num_tests", 0),
                    "Total Time (s)": total_time
                })
                
            # --- DATASET B: COMMON PROGRAMS ONLY (ALL STRATEGIES) ---
            if strategy in strat_data_map:
                data = strat_data_map[strategy]
                
                common_time = 0
                common_test_counts = []
                
                timing_data = data.get("timing", {}).get("per_program", {})
                test_counts_data = data.get("test_counts", {}).get("per_program", {})
                
                for prog in common_programs:
                    # Some entries might still have the .dfy extension in the keys, so check both
                    prog_key = prog if prog in timing_data else f"{prog}.dfy"
                    
                    # Recalculate Time
                    if prog_key in timing_data:
                        common_time += timing_data[prog_key].get("test_gen_time", 0) + timing_data[prog_key].get("safety_check_time", 0)
                    
                    # Accumulate Test Counts for common programs
                    if prog_key in test_counts_data:
                        common_test_counts.append(test_counts_data[prog_key])
                        
                # Recalculate Statuses
                killed, survived, timeout, error = 0, 0, 0, 0
                for res in data.get("results", []):
                    prog_name = res.get("original_name", "").replace(".dfy", "")
                    if prog_name in common_programs:
                        st = res.get("status", "")
                        if st == "killed": killed += 1
                        elif st == "survived": survived += 1
                        elif st == "timeout": timeout += 1
                        elif st == "error": error += 1
                        
                total_common_mutants = killed + survived + timeout + error
                common_kill_rate = killed / total_common_mutants if total_common_mutants > 0 else 0
                
                # Recalculate Test Stats
                total_common_tests = sum(common_test_counts)
                avg_common_tests = (total_common_tests / len(common_test_counts)) if common_test_counts else 0.0
                median_common_tests = statistics.median(common_test_counts) if common_test_counts else 0
                
                records_common.append({
                    "X": x,
                    "Strategy": clean_name,
                    "Kill Rate": common_kill_rate,
                    "Killed": killed,
                    "Survived": survived,
                    "Timeout": timeout,
                    "Error": error,
                    "Total Time (s)": common_time,
                    "Total Number of Tests": total_common_tests,
                    "Average Number of Tests": avg_common_tests,
                    "Median Number of Tests": median_common_tests
                })
            
    return pd.DataFrame(records_full), pd.DataFrame(records_common)

# ==========================================
# Plotting Functions
# ==========================================

def plot_kill_rate_vs_x(df, out_dir, suffix=""):
    plt.figure(figsize=(7, 5))
    ax = sns.lineplot(
        data=df, x="X", y="Kill Rate", hue="Strategy", 
        style="Strategy", palette=STRATEGY_COLORS, markers=STRATEGY_MARKERS, 
        dashes=False, linewidth=2, markersize=8
    )
    plt.title("Mutant Kill Rate by Repeat Factor (X)")
    plt.xlabel("Repeat Factor (X)")
    plt.ylabel("Kill Rate")
    plt.xticks([1, 2, 3, 4, 5, 6, 7])
    
    vals = ax.get_yticks()
    ax.set_yticklabels(['{:,.1%}'.format(x) for x in vals])
    plt.legend(title="Strategy")
    plt.savefig(os.path.join(out_dir, f"plot_1_kill_rate_vs_x{suffix}.png"))
    plt.close()

def plot_time_vs_x(df, out_dir, suffix=""):
    plt.figure(figsize=(7, 5))
    sns.lineplot(
        data=df, x="X", y="Total Time (s)", hue="Strategy", 
        style="Strategy", palette=STRATEGY_COLORS, markers=STRATEGY_MARKERS, 
        dashes=False, linewidth=2, markersize=8
    )
    plt.title("Computational Cost by Repeat Factor (X)")
    plt.xlabel("Repeat Factor (X)")
    plt.ylabel("Total Execution Time (seconds)")
    plt.xticks([1, 2, 3, 4, 5, 6, 7])
    
    plt.legend(title="Strategy")
    plt.savefig(os.path.join(out_dir, f"plot_2_time_vs_x{suffix}.png"))
    plt.close()

def plot_efficiency_tradeoff(df, out_dir, suffix=""):
    plt.figure(figsize=(7, 5))
    ax = sns.scatterplot(
        data=df, x="Total Time (s)", y="Kill Rate", hue="Strategy", 
        style="Strategy", palette=STRATEGY_COLORS, markers=STRATEGY_MARKERS, 
        size="X", sizes=(50, 200)
    )
    plt.title("Efficiency Trade-off: Time vs. Kill Rate")
    plt.xlabel("Total Execution Time (seconds)")
    plt.ylabel("Kill Rate")
    
    vals = ax.get_yticks()
    ax.set_yticklabels(['{:,.1%}'.format(x) for x in vals])
    h, l = ax.get_legend_handles_labels()
    plt.legend(h, l, bbox_to_anchor=(1.05, 1), loc=2, borderaxespad=0.)
    plt.savefig(os.path.join(out_dir, f"plot_3_efficiency_tradeoff{suffix}.png"), bbox_inches='tight')
    plt.close()

def plot_status_breakdown(df, out_dir, target_x=7, suffix=""):
    df_x = df[df["X"] == target_x]
    if df_x.empty:
        return
        
    df_x = df_x.set_index("Strategy")
    status_df = df_x[["Killed", "Survived", "Timeout", "Error"]]
    colors = ["#4C72B0", "#DD8452", "#C44E52", "#8C8C8C"]
    
    ax = status_df.plot(kind="bar", stacked=True, figsize=(7, 5), color=colors, edgecolor='black')
    plt.title(f"Mutant Resolution Breakdown (X={target_x})")
    plt.xlabel("Strategy")
    plt.ylabel("Number of Mutants")
    plt.xticks(rotation=0)
    
    plt.legend(title="Status", bbox_to_anchor=(1.05, 1), loc='upper left')
    plt.savefig(os.path.join(out_dir, f"plot_4_status_breakdown_x{target_x}{suffix}.png"), bbox_inches='tight')
    plt.close()

def plot_total_tests_vs_x(df, out_dir, suffix=""):
    plt.figure(figsize=(7, 5))
    sns.lineplot(
        data=df, x="X", y="Total Number of Tests", hue="Strategy", 
        style="Strategy", palette=STRATEGY_COLORS, markers=STRATEGY_MARKERS, 
        dashes=False, linewidth=2, markersize=8
    )
    plt.title("Total Number of Tests by Repeat Factor (X)")
    plt.xlabel("Repeat Factor (X)")
    plt.ylabel("Total Tests Generated")
    plt.xticks([1, 2, 3, 4, 5, 6, 7])
    
    plt.legend(title="Strategy")
    plt.savefig(os.path.join(out_dir, f"plot_5_total_tests_vs_x{suffix}.png"))
    plt.close()

def plot_test_efficiency_tradeoff(df, out_dir, suffix=""):
    plt.figure(figsize=(7, 5))
    ax = sns.scatterplot(
        data=df, x="Total Number of Tests", y="Kill Rate", hue="Strategy", 
        style="Strategy", palette=STRATEGY_COLORS, markers=STRATEGY_MARKERS, 
        size="X", sizes=(50, 200)
    )
    plt.title("Test Efficiency: Volume vs. Kill Rate")
    plt.xlabel("Total Number of Tests")
    plt.ylabel("Kill Rate")
    
    vals = ax.get_yticks()
    ax.set_yticklabels(['{:,.1%}'.format(x) for x in vals])
    h, l = ax.get_legend_handles_labels()
    plt.legend(h, l, bbox_to_anchor=(1.05, 1), loc=2, borderaxespad=0.)
    plt.savefig(os.path.join(out_dir, f"plot_6_test_efficiency_tradeoff{suffix}.png"), bbox_inches='tight')
    plt.close()

def plot_avg_tests_vs_mutation_score(df, out_dir, suffix=""):
    plt.figure(figsize=(7, 5))
    ax = sns.scatterplot(
        data=df, x="Average Number of Tests", y="Kill Rate", hue="Strategy", 
        style="Strategy", palette=STRATEGY_COLORS, markers=STRATEGY_MARKERS, 
        size="X", sizes=(50, 200)
    )
    plt.title("Kill Rate vs. Avg Tests per Mutant")
    plt.xlabel("Average Number of Tests per Mutant")
    plt.ylabel("Kill Rate")
    
    vals = ax.get_yticks()
    ax.set_yticks(vals)
    ax.set_yticklabels(['{:,.1%}'.format(x) for x in vals])
    h, l = ax.get_legend_handles_labels()
    plt.legend(h, l, bbox_to_anchor=(1.05, 1), loc=2, borderaxespad=0.)
    plt.savefig(os.path.join(out_dir, f"plot_7_avg_tests_vs_mutation_score{suffix}.png"), bbox_inches='tight')
    plt.close()


if __name__ == "__main__":
    output_directory = "results"
    graphs_directory = os.path.join(output_directory, "graphs")
    
    os.makedirs(output_directory, exist_ok=True)
    os.makedirs(graphs_directory, exist_ok=True)

    print("Loading data...")
    df_full, df_common = load_data(output_directory)
    
    if df_full.empty and df_common.empty:
        print("No data loaded. Check your folder structure.")
    else:
        if not df_full.empty:
            print("Generating plots for FULLY SUPPORTED strategies...")
            plot_kill_rate_vs_x(df_full, graphs_directory, "_full_support")
            plot_time_vs_x(df_full, graphs_directory, "_full_support")
            plot_efficiency_tradeoff(df_full, graphs_directory, "_full_support")
            plot_status_breakdown(df_full, graphs_directory, target_x=7, suffix="_full_support")
            plot_total_tests_vs_x(df_full, graphs_directory, "_full_support")
            plot_test_efficiency_tradeoff(df_full, graphs_directory, "_full_support")
            plot_avg_tests_vs_mutation_score(df_full, graphs_directory, "_full_support")
            
        if not df_common.empty:
            print("Generating plots for ALL strategies on COMMON programs...")
            plot_kill_rate_vs_x(df_common, graphs_directory, "_common_programs")
            plot_time_vs_x(df_common, graphs_directory, "_common_programs")
            plot_efficiency_tradeoff(df_common, graphs_directory, "_common_programs")
            plot_status_breakdown(df_common, graphs_directory, target_x=7, suffix="_common_programs")
            plot_total_tests_vs_x(df_common, graphs_directory, "_common_programs")
            plot_test_efficiency_tradeoff(df_common, graphs_directory, "_common_programs")
            plot_avg_tests_vs_mutation_score(df_common, graphs_directory, "_common_programs")
            
        print(f"Done! Check the '{graphs_directory}' directory for the generated .png files.")