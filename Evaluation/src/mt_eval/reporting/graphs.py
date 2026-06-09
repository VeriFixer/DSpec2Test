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
    'font.family': 'serif'
})

STRATEGY_COLORS = {
    "Block": "#1f77b4",
    "Path": "#ff7f0e",
    "Spec": "#2ca02c",
    "Spec_bva": "#d62728"
}

STRATEGY_MARKERS = {
    "Block": "o",
    "Path": "s",
    "Spec": "^",
    "Spec_bva": "D"
}

# ==========================================
# Data Processing
# ==========================================

def get_max_repetition(base_dir):
    """
    Scans the folder structure to find the highest repetition (X) value dynamically.
    """
    max_x = 0
    if not os.path.exists(base_dir):
        return max_x
        
    for item in os.listdir(base_dir):
        strat_dir = os.path.join(base_dir, item)
        if os.path.isdir(strat_dir) and item.startswith("results_"):
            for file in os.listdir(strat_dir):
                if "_rep_" in file and file.endswith(".json"):
                    try:
                        x_str = file.split("_rep_")[-1].replace(".json", "")
                        max_x = max(max_x, int(x_str))
                    except ValueError:
                        pass
    return max_x


def get_shared_programs_for_combo(base_dir, combo_strategies, max_x):
    """
    Finds the exact set of programs that are supported by ALL strategies 
    in the given combination, across all X repetitions.
    """
    all_encountered = set()
    unsupported_in_combo = set()
    
    for x in range(1, max_x + 1):
        for strategy in combo_strategies:
            strat_path = os.path.join(base_dir, f"results_{strategy}", f"results_{strategy}_rep_{x}.json")
            
            if os.path.exists(strat_path):
                with open(strat_path, 'r') as sf:
                    data = json.load(sf)
                
                # 1. Track every program we've ever seen
                timing_data = data.get("timing", {}).get("per_program", {})
                for prog in timing_data.keys():
                    all_encountered.add(prog.replace(".dfy", ""))
                
                # 2. Track failures for strategies in this combination
                not_supported_list = data.get("not_supported", [])
                for item in not_supported_list:
                    if isinstance(item, dict) and "program" in item:
                        unsupported_in_combo.add(item["program"].replace(".dfy", ""))

    # The intersection of supported programs is the total minus the failures of this combo
    shared_programs = all_encountered - unsupported_in_combo
    return shared_programs


def load_data_for_subset(base_dir, valid_programs, combo_strategies, max_x):
    """
    Builds a DataFrame calculating metrics strictly for the given combination of strategies,
    evaluating them ONLY on the explicitly provided list of valid_programs.
    """
    records = []
    
    for x in range(1, max_x + 1):
        for strategy in combo_strategies:
            # Updated path structure
            strat_path = os.path.join(base_dir, f"results_{strategy}", f"results_{strategy}_rep_{x}.json")
            if not os.path.exists(strat_path):
                continue
                
            with open(strat_path, 'r') as sf:
                data = json.load(sf)
                
            common_time = 0
            common_test_counts = []
            
            timing_data = data.get("timing", {}).get("per_program", {})
            test_counts_data = data.get("test_counts", {}).get("per_program", {})
            
            # 1. Recalculate Time and Test Counts
            for prog in valid_programs:
                prog_key = prog if prog in timing_data else f"{prog}.dfy"
                
                if prog_key in timing_data:
                    common_time += timing_data[prog_key].get("test_gen_time", 0) + timing_data[prog_key].get("safety_check_time", 0)
                
                if prog_key in test_counts_data:
                    common_test_counts.append(test_counts_data[prog_key])
                    
            # 2. Recalculate Mutant Statuses
            killed, survived, timeout, error = 0, 0, 0, 0
            for res in data.get("results", []):
                prog_name = res.get("original_name", "").replace(".dfy", "")
                if prog_name in valid_programs:
                    st = res.get("status", "")
                    if st == "killed": killed += 1
                    elif st == "survived": survived += 1
                    elif st == "timeout": timeout += 1
                    elif st == "error": error += 1
                    
            # 3. Final calculations for this X and Strategy
            total_common_mutants = killed + survived + timeout + error

            # Change to (killed), if do not wish to count timeouts as kills
            common_kill_rate = (killed) / total_common_mutants if total_common_mutants > 0 else 0
            
            total_common_tests = sum(common_test_counts)
            avg_common_tests = (total_common_tests / len(common_test_counts)) if common_test_counts else 0.0
            median_common_tests = statistics.median(common_test_counts) if common_test_counts else 0
            
            records.append({
                "X": x,
                "Strategy": strategy,
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
            
    return pd.DataFrame(records)

# ==========================================
# Plotting Functions
# ==========================================
# Note: Dynamic X-axis adjustments made to accommodate variable max_x

def plot_kill_rate_vs_x(df, out_dir, suffix=""):
    max_x = int(df["X"].max())
    plt.figure(figsize=(7, 5))
    ax = sns.lineplot(
        data=df, x="X", y="Kill Rate", hue="Strategy", 
        style="Strategy", palette=STRATEGY_COLORS, markers=STRATEGY_MARKERS, 
        dashes=False, linewidth=2, markersize=8
    )
    plt.title("Mutant Kill Rate by Repeat Factor (X)")
    plt.xlabel("Repeat Factor (X)")
    plt.ylabel("Kill Rate")
    plt.xticks(range(1, max_x + 1))
    
    vals = ax.get_yticks()
    ax.set_yticks(vals)
    ax.set_yticklabels(['{:,.1%}'.format(x) for x in vals])
    plt.legend(title="Strategy")
    plt.savefig(os.path.join(out_dir, f"plot_1_kill_rate_vs_x{suffix}.png"))
    plt.close()

def plot_time_vs_x(df, out_dir, suffix=""):
    max_x = int(df["X"].max())
    plt.figure(figsize=(7, 5))
    sns.lineplot(
        data=df, x="X", y="Total Time (s)", hue="Strategy", 
        style="Strategy", palette=STRATEGY_COLORS, markers=STRATEGY_MARKERS, 
        dashes=False, linewidth=2, markersize=8
    )
    plt.title("Computational Cost by Repeat Factor (X)")
    plt.xlabel("Repeat Factor (X)")
    plt.ylabel("Total Execution Time (seconds)")
    plt.xticks(range(1, max_x + 1))
    
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
    ax.set_yticks(vals)
    ax.set_yticklabels(['{:,.1%}'.format(x) for x in vals])
    h, l = ax.get_legend_handles_labels()
    plt.legend(h, l, bbox_to_anchor=(1.05, 1), loc=2, borderaxespad=0.)
    plt.savefig(os.path.join(out_dir, f"plot_3_efficiency_tradeoff{suffix}.png"), bbox_inches='tight')
    plt.close()

def plot_status_breakdown(df, out_dir, target_x, suffix=""):
    df_x = df[df["X"] == target_x]
    if df_x.empty:
        return
        
    df_x = df_x.set_index("Strategy")
    status_df = df_x[["Killed", "Timeout", "Survived", "Error"]]
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
    max_x = int(df["X"].max())
    plt.figure(figsize=(7, 5))
    sns.lineplot(
        data=df, x="X", y="Total Number of Tests", hue="Strategy", 
        style="Strategy", palette=STRATEGY_COLORS, markers=STRATEGY_MARKERS, 
        dashes=False, linewidth=2, markersize=8
    )
    plt.title("Total Number of Tests by Repeat Factor (X)")
    plt.xlabel("Repeat Factor (X)")
    plt.ylabel("Total Tests Generated")
    plt.xticks(range(1, max_x + 1))
    
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
    ax.set_yticks(vals)
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

    # Detect the max X dynamically
    max_x = get_max_repetition(output_directory)
    print(f"Dynamically detected Maximum Repetition (X) = {max_x}")

    if max_x == 0:
        print("No valid repetition files found. Please check your results directory.")
        exit()

    # 1. Define the combinations you want to analyze
    combinations_to_run = [
        {
            "name": "Block_Spec_SpecBva",
            "strategies": ["Block", "Spec", "Spec_bva"]
        },
        {
            "name": "All_Strategies",
            "strategies": ["Block", "Path", "Spec", "Spec_bva"]
        }
    ]

    for combo in combinations_to_run:
        combo_name = combo["name"]
        combo_strats = combo["strategies"]
        
        print(f"\n" + "="*55)
        print(f"Processing Combination: {combo_strats}")
        print("="*55)
        
        # Pass the max_x to the data processor
        valid_programs = get_shared_programs_for_combo(output_directory, combo_strats, max_x)
        print(f"-> Found {len(valid_programs)} commonly supported programs.")
        
        if len(valid_programs) == 0:
            print(f"-> Skipping {combo_name} due to 0 shared programs.")
            continue
            
        # Build DataFrame explicitly for these strategies and this subset of programs
        df_combo = load_data_for_subset(output_directory, valid_programs, combo_strats, max_x)
        
        if df_combo.empty:
            print(f"-> Error: No data could be loaded for {combo_name}.")
            continue
            
        # Plotting
        suffix = f"_{combo_name}"
        print(f"-> Generating plots with suffix '{suffix}'...")
        plot_kill_rate_vs_x(df_combo, graphs_directory, suffix)
        plot_time_vs_x(df_combo, graphs_directory, suffix)
        plot_efficiency_tradeoff(df_combo, graphs_directory, suffix)
        plot_status_breakdown(df_combo, graphs_directory, target_x=max_x, suffix=suffix)
        plot_total_tests_vs_x(df_combo, graphs_directory, suffix)
        plot_test_efficiency_tradeoff(df_combo, graphs_directory, suffix)
        plot_avg_tests_vs_mutation_score(df_combo, graphs_directory, suffix)
        
    print(f"\nDone! Check the '{graphs_directory}' directory for all generated files.")