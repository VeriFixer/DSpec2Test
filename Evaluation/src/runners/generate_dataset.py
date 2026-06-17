import csv
import sys
import re
import argparse
import time
from pathlib import Path

from src.config import CSV_ROOT, EXTERNAL_ROOT, SELECTED_PROGRAMS_DIR
from src.logging_config import get_logger

logger = get_logger(__name__)

KEYWORDS = {"array", "array2", "class", "->", "-->", "~>"}

def filter_and_copy_dafny_programs(csv_name: str):
    csv_path = Path(CSV_ROOT) / csv_name
    ground_truth_dir = Path(EXTERNAL_ROOT) / "bench" / "dafnybench" / "DafnyBench" / "dataset" / "ground_truth"
    
    if not csv_path.exists():
        logger.error(f"CSV file not found at {csv_path}")
        return

    SELECTED_PROGRAMS_DIR.mkdir(parents=True, exist_ok=True)

    total_csv_files = 0
    dafnybench_files = 0
    methods_files = 0
    copied_files = 0

    keyword_patterns = [re.compile(rf'\b{re.escape(kw)}\b') for kw in KEYWORDS]
    method_pattern = re.compile(r'\bmethod\b')

    logger.info(f"Starting to process {csv_name}...")
    
    with open(csv_path, mode='r', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        
        for row in reader:
            total_csv_files += 1
            benchmark_name = row.get("benchmark_name", "").strip()
            program_name = row.get("program_name", "").strip()

            if benchmark_name == "DafnyBench":
                dafnybench_files += 1

                matched_files = list(ground_truth_dir.glob(f"{program_name}.dfy"))
                
                if not matched_files:
                    logger.warning(f"Source file for '{program_name}' not found in ground_truth dir.")
                    continue

                src_file = matched_files[0] 

                try:
                    with open(src_file, 'r', encoding='utf-8') as src_f:
                        content = src_f.read()

                    has_method = bool(method_pattern.search(content))

                    if not has_method:
                        continue

                    methods_files += 1

                    contains_keyword = any(pattern.search(content) for pattern in keyword_patterns)

                    if not contains_keyword:

                        dest_file = SELECTED_PROGRAMS_DIR / src_file.name

                        modified_content = re.sub(r'\bmethod\b', 'method {:testEntry}', content)

                        with open(dest_file, 'w', encoding='utf-8') as dest_f:
                            dest_f.write(modified_content)

                        copied_files += 1

                except Exception as e:
                    logger.error(f"Error reading or copying {src_file.name}: {e}")

    logger.info("=== Execution Summary ===")
    logger.info(f"Total files in CSV:           {total_csv_files}")
    logger.info(f"Files from DafnyBench:        {dafnybench_files}")
    logger.info(f"Files with methods:           {methods_files}")
    logger.info(f"Files copied (no keywords):   {copied_files}")
    logger.info("=========================")
    return 0


def parse_args(argv=None):
    """Parse CLI arguments for dataset filtering."""
    parser = argparse.ArgumentParser(description="Filter and copy Dafny programs.")
    parser.add_argument(
        "--file", 
        required=True, 
        help="The name of the CSV file (located in CSV_ROOT) to process."
    )
    return parser.parse_args(argv)


def main(argv=None):
    start_time = time.time()

    args = parse_args(argv)
    
    r = filter_and_copy_dafny_programs(args.file)

    end_time = time.time()
    elapsed_time = end_time - start_time
    logger.info(f"Total execution time: {elapsed_time:.4f} seconds")
    sys.exit(r)


if __name__ == "__main__":
    main()