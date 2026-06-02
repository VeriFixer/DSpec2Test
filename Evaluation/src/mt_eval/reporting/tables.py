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
                    "Kill Rate": (stats.get("killed", 0) + stats.get("timeout", 0)) / stats.get("supported_mutants", 1),
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
                common_kill_rate = (killed + timeout) / total_common_mutants if total_common_mutants > 0 else 0
                
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
# Table Generation Functions
# ==========================================

def generate_tables(df, out_dir, suffix=""):
    """
    Generates summary tables and exports them to CSV and LaTeX formats.
    """
    tables_dir = os.path.join(out_dir, "tables")
    os.makedirs(tables_dir, exist_ok=True)
    
    # Helper to save tables
    def save_table(table_df, name):
        # Save to CSV
        table_df.to_csv(os.path.join(tables_dir, f"{name}{suffix}.csv"))
        # Save to LaTeX
        with open(os.path.join(tables_dir, f"{name}{suffix}.tex"), "w") as f:
            f.write(table_df.to_latex(float_format="%.2f"))

    # ---------------------------------------------------------
    # Table 1: Overall Performance Summary at X = 7
    # ---------------------------------------------------------
    max_x = df["X"].max()
    df_max_x = df[df["X"] == max_x].copy()
    
    if not df_max_x.empty:
        summary_cols = ["Strategy", "Kill Rate", "Total Time (s)", 
                        "Total Number of Tests", "Average Number of Tests"]
        table1 = df_max_x[summary_cols].set_index("Strategy").copy()
        
        # Format Kill Rate as percentage string for presentation
        table1["Kill Rate (%)"] = (table1["Kill Rate"] * 100).round(2)
        table1 = table1.drop(columns=["Kill Rate"])
        
        # Reorder columns nicely
        table1 = table1[["Kill Rate (%)", "Total Time (s)", "Total Number of Tests", "Average Number of Tests"]]
        save_table(table1, f"table_1_summary_x{max_x}")

    # ---------------------------------------------------------
    # Table 2: Kill Rate Progression across X (Diminishing Returns)
    # ---------------------------------------------------------
    # Pivot: Index=Strategy, Columns=X, Values=Kill Rate
    table2 = df.pivot(index="Strategy", columns="X", values="Kill Rate")
    # Convert to percentages
    table2 = (table2 * 100).round(2)
    # Rename columns to indicate X
    table2.columns = [f"X={col}" for col in table2.columns]
    save_table(table2, "table_2_kill_rate_progression")

    # ---------------------------------------------------------
    # Table 3: Execution Time Progression across X
    # ---------------------------------------------------------
    table3 = df.pivot(index="Strategy", columns="X", values="Total Time (s)")
    table3 = table3.round(2)
    table3.columns = [f"X={col}" for col in table3.columns]
    save_table(table3, "table_3_time_progression")

    # ---------------------------------------------------------
    # Table 4: Mutant Resolution Breakdown at Max X
    # ---------------------------------------------------------
    if not df_max_x.empty:
        table4 = df_max_x[["Strategy", "Killed", "Survived", "Timeout", "Error"]].set_index("Strategy")
        save_table(table4, f"table_4_status_breakdown_x{max_x}")

    # ---------------------------------------------------------
    # Table 5: Mutant Resolution Evolution across X
    # ---------------------------------------------------------
    # We use a multi-index (Strategy, then X) to keep the table narrow enough for a paper
    table5 = df.set_index(["X", "Strategy"])[["Killed", "Survived", "Timeout", "Error"]].copy()
    table5 = table5.sort_index()
    table5 = table5.astype(int)
    save_table(table5, "table_5_status_evolution")


if __name__ == "__main__":
    output_directory = "results"
    tables_directory = os.path.join(output_directory, "tables")
    
    os.makedirs(output_directory, exist_ok=True)
    os.makedirs(tables_directory, exist_ok=True)

    print("Loading data...")
    df_full, df_common = load_data(output_directory)
    
    if df_full.empty and df_common.empty:
        print("No data loaded. Check your folder structure.")
    else:
        if not df_full.empty:
            generate_tables(df_full, output_directory, "_full_support")
            
        if not df_common.empty:
            generate_tables(df_common, output_directory, "_common_programs")
            
        print(f"Done! Check the '{tables_directory}' directory for tables.")