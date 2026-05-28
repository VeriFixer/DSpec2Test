import re
import statistics
import json
from pathlib import Path
from typing import Union, Dict, Any

def get_test_count(dfy_file: Union[str, Path]) -> int:
    """Parses a single Dafny file and returns the total number of test methods."""
    file_path = Path(dfy_file)
    
    if not file_path.exists() or not file_path.is_file():
        return 0
        
    try:
        content = file_path.read_text(encoding='utf-8')
    except UnicodeDecodeError:
        print(f"Warning: Could not read {file_path} due to encoding issues. Skipping.")
        return 0
        
    pattern = re.compile(r'method\s+\{\s*:test\}\s+([a-zA-Z0-9_]+)')
    return len(set(pattern.findall(content)))

def get_test_statistics(directory: Union[str, Path], file_pattern: str = "*.dfy") -> Dict[str, Any]:
    """Recursively calculates test statistics for files matching the pattern."""
    dir_path = Path(directory)
    
    if not dir_path.exists() or not dir_path.is_dir():
        print(f"Warning: Directory not found at {dir_path}")
        return {"total": 0, "average": 0, "median": 0, "files_scanned": 0, "per_program_map": {}}
        
    # Use a dictionary to map the program stem to its test count
    test_count_map = {}
    
    for dfy_file in dir_path.rglob(file_pattern):
        count = get_test_count(dfy_file)
        
        # Extract the original program stem 
        # (e.g., 'RollingMax.test.dfy' -> 'RollingMax')
        stem = dfy_file.name.replace('.test.dfy', '').replace('.dfy', '')
        test_count_map[stem] = count
        
    counts_list = list(test_count_map.values())
    
    # Handle the case where no files were found to avoid division by zero
    if not counts_list:
        return {"total": 0, "average": 0, "median": 0, "files_scanned": 0, "per_program_map": {}}
        
    return {
        "total": sum(counts_list),
        "average": statistics.mean(counts_list),
        "median": statistics.median(counts_list),
        "files_scanned": len(counts_list),
        "per_program_map": test_count_map
    }

if __name__ == "__main__":
    target_directory = "./" 
    
    # Calculate all stats at once (change to "*.test.dfy" if scanning a tests folder)
    stats = get_test_statistics(target_directory, file_pattern="*.dfy")
    
    # Print the aggregate results
    print("=== Test Method Statistics ===")
    print(f"Files Scanned : {stats['files_scanned']}")
    print(f'"total_num_tests": {stats["total"]},')
    print(f'"avg_num_tests": {stats["average"]:.2f},')
    print(f'"median_num_tests": {stats["median"]:.2f}')
    print("==============================\n")

    # Print the JSON snippet to copy/paste
    print("=== JSON Snippet to Copy/Paste ===")
    
    # Create the exact structure you need
    output_snippet = {
        "test_counts": {
            "per_program": stats["per_program_map"]
        }
    }
    
    # Convert to a formatted JSON string
    json_str = json.dumps(output_snippet, indent=4)
    
    # Strip the outermost curly braces so you can easily paste it into an existing JSON object
    lines = json_str.split('\n')
    pasteable_str = '\n'.join(lines[1:-1]) 
    
    print(pasteable_str + ",")
    print("==================================")