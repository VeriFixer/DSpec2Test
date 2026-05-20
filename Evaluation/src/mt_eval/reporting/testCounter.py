import os
import re
import glob
import statistics
from collections import defaultdict

def get_test_methods(dfy_file):
    with open(dfy_file, 'r', encoding='utf-8') as f:
        content = f.read()
    pattern = re.compile(r'method\s+\{\s*:test[^}]*\}\s+([a-zA-Z0-9_]+)')
    return list(set(pattern.findall(content)))

def main():
    # Find all .dfy files in the current directory and subdirectories
    dfy_files = glob.glob("**/*.dfy", recursive=True)
    
    if not dfy_files:
        print("No .dfy files found in the current directory or subdirectories.")
        return

    # Dictionary to hold file stats grouped by top-level folder
    # Key: folder name, Value: list of tuples (file_path, test_count)
    folder_data = defaultdict(list)

    for dfy_file in dfy_files:
        try:
            tests = get_test_methods(dfy_file)
            count = len(tests)
            
            # Determine which top-level folder this file belongs to
            path_parts = os.path.normpath(dfy_file).split(os.sep)
            if len(path_parts) > 1:
                folder_name = path_parts[0]
            else:
                folder_name = "(root directory)"
                
            folder_data[folder_name].append((dfy_file, count))
            
        except Exception as e:
            print(f"Error reading {dfy_file}: {e}")

    # Calculate and print metrics per folder
    for folder, file_stats in sorted(folder_data.items()):
        counts = [c for _, c in file_stats]
        
        total_files = len(counts)
        total_tests = sum(counts)
        
        avg_tests = total_tests / total_files
        median_tests = statistics.median(counts)
        max_tests = max(counts)
        min_tests = min(counts)
        
        # Keep just the filename (not the full path) for cleaner output
        max_files = [os.path.basename(f) for f, c in file_stats if c == max_tests]
        
        zero_test_files = sum(1 for c in counts if c == 0)

        print(f"\n=== Metrics for: {folder} ===")

        print(f'"total_num_tests": {total_tests},')
        print(f'"avg_num_tests": {avg_tests:.2f},')
        print(f'"median_num_tests": {median_tests}')

        """ print(f"Total .dfy files:       {total_files}")
        print(f"Total test methods:     {total_tests}")
        print("-" * 31)
        print(f"Average tests per file: {avg_tests:.2f}")
        print(f"Median tests per file:  {median_tests}")
        print(f"Max tests in a file:    {max_tests}")
        print(f"Min tests in a file:    {min_tests}")
        print(f"Files with 0 tests:     {zero_test_files}")
        print() # blank line for readability """

if __name__ == "__main__":
    main()