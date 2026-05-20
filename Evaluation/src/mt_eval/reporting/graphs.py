import os
import json
import glob
import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns

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

def load_data(base_dir="../../../results"):
    """Parses the folder structure and JSON files into a Pandas DataFrame."""
    records = []
    
    # Iterate through results_1 to results_5
    for x in range(1, 6):
        folder_path = os.path.join(base_dir, f"results_{x}")
        comp_path = os.path.join(folder_path, "comparison.json")
        
        if not os.path.exists(comp_path):
            print(f"Warning: {comp_path} not found. Skipping X={x}.")
            continue
            
        with open(comp_path, 'r') as f:
            comp_data = json.load(f)
            
        for strategy, stats in comp_data.get("strategies", {}).items():
            # Clean strategy name for the legend (e.g., "DafnyTestGenerator_Spec" -> "Spec")
            clean_name = strategy.replace("DafnyTestGenerator_", "")
            
            record = {
                "X": x,
                "Strategy": clean_name,
                "Kill Rate": stats.get("kill_rate", 0),
                "Killed": stats.get("killed", 0),
                "Survived": stats.get("survived", 0),
                "Timeout": stats.get("timeout", 0),
                "Error": stats.get("error", 0),
                "Total Number of Tests": stats.get("total_num_tests", 0), # NEW
                "Average Number of Tests": stats.get("avg_num_tests", 0), # NEW
                "Median Number of Tests": stats.get("median_num_tests", 0), # NEW
            }
            
            # Find the specific results file for this strategy to calculate time
            # Exclude comparison.json just in case
            strat_files = [f for f in glob.glob(os.path.join(folder_path, f"*{strategy}*.json")) 
                           if "comparison" not in f]
            
            total_time = 0
            if strat_files:
                with open(strat_files[0], 'r') as sf:
                    strat_data = json.load(sf)
                    timing_data = strat_data.get("timing", {}).get("per_program", {})
                    # Sum test_gen_time and safety_check_time across all programs
                    for prog, times in timing_data.items():
                        total_time += times.get("test_gen_time", 0) + times.get("safety_check_time", 0)
            
            record["Total Time (s)"] = total_time
            records.append(record)
            
    return pd.DataFrame(records)

def plot_kill_rate_vs_x(df, out_dir):
    """Generates a line plot of X vs Kill Rate."""
    plt.figure(figsize=(7, 5))
    ax = sns.lineplot(
        data=df, x="X", y="Kill Rate", hue="Strategy", 
        style="Strategy", markers=["o", "s", "^"], dashes=False, 
        linewidth=2, markersize=8
    )
    
    plt.title("Mutant Kill Rate by Repeat Factor (X)")
    plt.xlabel("Repeat Factor (X)")
    plt.ylabel("Kill Rate")
    plt.xticks([1, 2, 3, 4, 5])
    
    # Format y-axis as percentage
    vals = ax.get_yticks()
    ax.set_yticklabels(['{:,.1%}'.format(x) for x in vals])
    
    plt.legend(title="Strategy")
    #plt.savefig(os.path.join(out_dir, "plot_1_kill_rate_vs_x.pdf"))
    plt.savefig(os.path.join(out_dir, "plot_1_kill_rate_vs_x.png"))
    plt.close()

def plot_time_vs_x(df, out_dir):
    """Generates a line plot of X vs Total Execution Time."""
    plt.figure(figsize=(7, 5))
    sns.lineplot(
        data=df, x="X", y="Total Time (s)", hue="Strategy", 
        style="Strategy", markers=["o", "s", "^"], dashes=False, 
        linewidth=2, markersize=8
    )
    
    plt.title("Computational Cost by Repeat Factor (X)")
    plt.xlabel("Repeat Factor (X)")
    plt.ylabel("Total Execution Time (seconds)")
    plt.xticks([1, 2, 3, 4, 5])
    
    plt.legend(title="Strategy")
    #plt.savefig(os.path.join(out_dir, "plot_2_time_vs_x.pdf"))
    plt.savefig(os.path.join(out_dir, "plot_2_time_vs_x.png"))
    plt.close()

def plot_efficiency_tradeoff(df, out_dir):
    """Generates a scatter plot showing Time vs Kill Rate."""
    plt.figure(figsize=(7, 5))
    
    # Use size of the marker to represent X
    sns.scatterplot(
        data=df, x="Total Time (s)", y="Kill Rate", hue="Strategy", 
        style="Strategy", size="X", sizes=(50, 200), markers=["o", "s", "^"]
    )
    
    plt.title("Efficiency Trade-off: Time vs. Kill Rate")
    plt.xlabel("Total Execution Time (seconds)")
    plt.ylabel("Kill Rate")
    
    # Format y-axis as percentage
    ax = plt.gca()
    vals = ax.get_yticks()
    ax.set_yticklabels(['{:,.1%}'.format(x) for x in vals])
    
    # Customize legend
    h, l = ax.get_legend_handles_labels()
    plt.legend(h, l, bbox_to_anchor=(1.05, 1), loc=2, borderaxespad=0.)
    
    #plt.savefig(os.path.join(out_dir, "plot_3_efficiency_tradeoff.pdf"), bbox_inches='tight')
    plt.savefig(os.path.join(out_dir, "plot_3_efficiency_tradeoff.png"), bbox_inches='tight')
    plt.close()

def plot_status_breakdown(df, out_dir, target_x=5):
    """Generates a stacked bar chart of mutant statuses for a specific X."""
    df_x = df[df["X"] == target_x].set_index("Strategy")
    
    # Select only the status columns
    status_df = df_x[["Killed", "Survived", "Timeout", "Error"]]
    
    # Define colors for scientific clarity (Green, Orange, Red, Grey)
    colors = ["#4C72B0", "#DD8452", "#C44E52", "#8C8C8C"]
    
    ax = status_df.plot(kind="bar", stacked=True, figsize=(7, 5), color=colors, edgecolor='black')
    
    plt.title(f"Mutant Resolution Breakdown (X={target_x})")
    plt.xlabel("Strategy")
    plt.ylabel("Number of Mutants")
    plt.xticks(rotation=0)
    
    plt.legend(title="Status", bbox_to_anchor=(1.05, 1), loc='upper left')
    #plt.savefig(os.path.join(out_dir, f"plot_4_status_breakdown_x{target_x}.pdf"), bbox_inches='tight')
    plt.savefig(os.path.join(out_dir, f"plot_4_status_breakdown_x{target_x}.png"), bbox_inches='tight')
    plt.close()


def plot_total_tests_vs_x(df, out_dir):
    """Generates a line plot of X vs Total Number of Tests."""
    plt.figure(figsize=(7, 5))
    sns.lineplot(
        data=df, x="X", y="Total Number of Tests", hue="Strategy", 
        style="Strategy", markers=["o", "s", "^"], dashes=False, 
        linewidth=2, markersize=8
    )
    
    plt.title("Total Number of Tests by Repeat Factor (X)")
    plt.xlabel("Repeat Factor (X)")
    plt.ylabel("Total Tests Generated")
    plt.xticks([1, 2, 3, 4, 5])
    
    plt.legend(title="Strategy")
    #plt.savefig(os.path.join(out_dir, "plot_5_total_tests_vs_x.pdf"))
    plt.savefig(os.path.join(out_dir, "plot_5_total_tests_vs_x.png"))
    plt.close()

def plot_test_efficiency_tradeoff(df, out_dir):
    """Generates a scatter plot showing Total Tests vs Kill Rate."""
    plt.figure(figsize=(7, 5))
    
    ax = sns.scatterplot(
        data=df, x="Total Number of Tests", y="Kill Rate", hue="Strategy", 
        style="Strategy", size="X", sizes=(50, 200), markers=["o", "s", "^"]
    )
    
    plt.title("Test Efficiency: Volume vs. Kill Rate")
    plt.xlabel("Total Number of Tests")
    plt.ylabel("Kill Rate")
    
    # Format y-axis as percentage
    vals = ax.get_yticks()
    ax.set_yticklabels(['{:,.1%}'.format(x) for x in vals])
    
    # Customize legend to sit outside the plot
    h, l = ax.get_legend_handles_labels()
    plt.legend(h, l, bbox_to_anchor=(1.05, 1), loc=2, borderaxespad=0.)
    
    #plt.savefig(os.path.join(out_dir, "plot_6_test_efficiency_tradeoff.pdf"), bbox_inches='tight')
    plt.savefig(os.path.join(out_dir, "plot_6_test_efficiency_tradeoff.png"), bbox_inches='tight')
    plt.close()


if __name__ == "__main__":
    output_directory = "../../../results"
    os.makedirs(output_directory, exist_ok=True)

    print("Loading data...")
    df = load_data()
    
    if df.empty:
        print("No data loaded. Check your folder structure.")
    else:
        print("Data loaded successfully. Generating plots...")
        
        plot_kill_rate_vs_x(df, output_directory)
        plot_time_vs_x(df, output_directory)
        plot_efficiency_tradeoff(df, output_directory)
        plot_status_breakdown(df, output_directory, target_x=5)
        plot_total_tests_vs_x(df, output_directory)
        plot_test_efficiency_tradeoff(df, output_directory)
        
        print("Done! Check your directory for the generated .png files.")