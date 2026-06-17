import os
import json
import statistics
import pandas as pd

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
                
                timing_data = data.get("timing", {}).get("per_program", {})
                for prog in timing_data.keys():
                    all_encountered.add(prog.replace(".dfy", ""))
                
                not_supported_list = data.get("not_supported", [])
                for item in not_supported_list:
                    if isinstance(item, dict) and "program" in item:
                        unsupported_in_combo.add(item["program"].replace(".dfy", ""))

    shared_programs = all_encountered - unsupported_in_combo
    return shared_programs

# ==========================================
# Data Processing
# ==========================================

def load_data_for_subset(base_dir, valid_programs, combo_strategies, max_x):
    """
    Builds a DataFrame calculating metrics strictly for the given combination of strategies,
    evaluating them ONLY on the explicitly provided list of valid_programs.
    """
    records = []
    
    for x in range(1, max_x + 1):
        for strategy in combo_strategies:
            strat_path = os.path.join(base_dir, f"results_{strategy}", f"results_{strategy}_rep_{x}.json")
            if not os.path.exists(strat_path):
                continue
                
            with open(strat_path, 'r') as sf:
                data = json.load(sf)
                
            common_test_gen_time = 0.0
            common_safety_check_time = 0.0
            common_execution_time = 0.0
            common_test_counts = []
            
            timing_data = data.get("timing", {}).get("per_program", {})
            test_counts_data = data.get("test_counts", {}).get("per_program", {})
            
            for prog in valid_programs:
                prog_key = prog if prog in timing_data else f"{prog}.dfy"
                if prog_key in timing_data:
                    common_test_gen_time += timing_data[prog_key].get("test_gen_time", 0.0)
                    common_safety_check_time += timing_data[prog_key].get("safety_check_time", 0.0)
                if prog_key in test_counts_data:
                    common_test_counts.append(test_counts_data[prog_key])
                    
            killed, survived, timeout, error = 0, 0, 0, 0
            for res in data.get("results", []):
                prog_name = res.get("original_name", "").replace(".dfy", "")
                if prog_name in valid_programs:
                    st = res.get("status", "")
                    if st == "killed": killed += 1
                    elif st == "survived": survived += 1
                    elif st == "timeout": timeout += 1
                    elif st == "error" or st == "": error += 1
                    common_execution_time += res.get("execution_time", 0.0)
                    
            total_common_mutants = killed + survived + timeout + error
            num_programs = len(valid_programs)

            common_kill_rate = (killed + timeout) / total_common_mutants if total_common_mutants > 0 else 0
            
            avg_test_gen_time = common_test_gen_time / num_programs if num_programs > 0 else 0.0
            avg_safety_check_time = common_safety_check_time / num_programs if num_programs > 0 else 0.0
            avg_execution_time = common_execution_time / total_common_mutants if total_common_mutants > 0 else 0.0
            expected_pipeline_time = avg_test_gen_time + avg_safety_check_time + avg_execution_time
            
            total_common_tests = sum(common_test_counts)
            avg_common_tests = (total_common_tests / len(common_test_counts)) if common_test_counts else 0.0
            
            records.append({
                "X": x,
                "Strategy": "SpecBva" if strategy == "Spec_bva" else strategy,
                "Kill Rate": common_kill_rate,
                "Killed": killed,
                "Survived": survived,
                "Timeout": timeout,
                "Error": error,
                "Expected Pipeline Time (s)": expected_pipeline_time,
                "Avg Test Gen Time (s)": avg_test_gen_time,
                "Avg Safety Check Time (s)": avg_safety_check_time,
                "Avg Execution Time (s)": avg_execution_time,
                "Total Number of Tests": total_common_tests,
                "Average Number of Tests": avg_common_tests
            })
            
    return pd.DataFrame(records)

# ==========================================
# Table Generation Functions
# ==========================================

def generate_tables(df, out_dir, target_x, suffix=""):
    """
    Generates summary tables and exports them to CSV and LaTeX formats.
    """
    tables_dir = os.path.join(out_dir, "tables")
    os.makedirs(tables_dir, exist_ok=True)
    
    def save_table(table_df, name):
        table_df.to_csv(os.path.join(tables_dir, f"{name}{suffix}.csv"))
        with open(os.path.join(tables_dir, f"{name}{suffix}.tex"), "w") as f:
            f.write(table_df.to_latex(float_format="%.2f", escape=True))

    # ---------------------------------------------------------
    # Table 1: Overall Performance Summary at max X
    # ---------------------------------------------------------
    df_max_x = df[df["X"] == target_x].copy()
    
    if not df_max_x.empty:
        summary_cols = ["Strategy", "Kill Rate", "Expected Pipeline Time (s)", 
                        "Total Number of Tests", "Average Number of Tests"]
        table1 = df_max_x[summary_cols].set_index("Strategy").copy()
        
        table1["Kill Rate (%)"] = (table1["Kill Rate"] * 100).round(2)
        table1 = table1.drop(columns=["Kill Rate"])
        
        table1 = table1[["Kill Rate (%)", "Expected Pipeline Time (s)", "Total Number of Tests", "Average Number of Tests"]]
        save_table(table1, f"table_1_summary_x{target_x}")

    # ---------------------------------------------------------
    # Table 2: Kill Rate Progression across X
    # ---------------------------------------------------------
    table2 = df.pivot(index="Strategy", columns="X", values="Kill Rate")
    table2 = (table2 * 100).round(2)
    table2.columns = [f"Rep={col}" for col in table2.columns]
    save_table(table2, "table_2_kill_rate_progression")

    # ---------------------------------------------------------
    # Table 3: Expected Pipeline Time Progression across X
    # ---------------------------------------------------------
    table3 = df.pivot(index="Strategy", columns="X", values="Expected Pipeline Time (s)")
    table3 = table3.round(2)
    table3.columns = [f"Rep={col}" for col in table3.columns]
    save_table(table3, "table_3_time_progression")

    # ---------------------------------------------------------
    # Table 4: Mutant Resolution Breakdown at Max X
    # ---------------------------------------------------------
    if not df_max_x.empty:
        table4 = df_max_x[["Strategy", "Killed", "Survived", "Timeout", "Error"]].set_index("Strategy")
        save_table(table4, f"table_4_status_breakdown_x{target_x}")

    # ---------------------------------------------------------
    # Table 5: Mutant Resolution Evolution across X
    # ---------------------------------------------------------
    table5 = df.set_index(["X", "Strategy"])[["Killed", "Survived", "Timeout", "Error"]].copy()
    table5 = table5.sort_index()
    table5 = table5.astype(int)
    save_table(table5, "table_5_status_evolution")

    # ---------------------------------------------------------
    # Table 6: Time Cost Breakdown per Mutant at Max X
    # ---------------------------------------------------------
    if not df_max_x.empty:
        time_cols = ["Strategy", "Avg Test Gen Time (s)", "Avg Safety Check Time (s)", "Avg Execution Time (s)"]
        table6 = df_max_x[time_cols].set_index("Strategy").copy()
        table6 = table6.round(3) # Extra precision useful for small isolated execution times
        save_table(table6, f"table_6_time_breakdown_x{target_x}")


if __name__ == "__main__":
    output_directory = "results"
    
    if not os.path.exists(output_directory):
        print(f"Error: Directory '{output_directory}' not found.")
        exit()

    max_x = get_max_repetition(output_directory)
    print(f"Dynamically detected Maximum Repetition (X) = {max_x}")

    if max_x == 0:
        print("No valid repetition files found. Please check your results directory.")
        exit()

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
        print(f"Generating Tables for: {combo_name}")
        print("="*55)
        
        valid_programs = get_shared_programs_for_combo(output_directory, combo_strats, max_x)
        print(f"-> Found {len(valid_programs)} commonly supported programs.")
        
        if len(valid_programs) == 0:
            print(f"-> Skipping {combo_name} due to 0 shared programs.")
            continue
            
        df_combo = load_data_for_subset(output_directory, valid_programs, combo_strats, max_x)
        
        if df_combo.empty:
            print(f"-> Error: No data could be loaded for {combo_name}.")
            continue
            
        suffix = f"_{combo_name}"
        generate_tables(df_combo, output_directory, target_x=max_x, suffix=suffix)
        
    print(f"\nDone! Check the 'results/tables' directory for all generated CSV and LaTeX files.")