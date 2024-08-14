import os
import csv
import json
from collections import Counter

# Define directories
base_dir = os.getcwd()
results_dir = os.path.join(base_dir, '..', 'results_summary')
error_dir = os.path.join(base_dir, 'error_results')

# Ensure error_results directory exists
os.makedirs(error_dir, exist_ok=True)

def process_csv_files():
    error_files = {}
    all_failed_files = []

    for filename in os.listdir(results_dir):
        if filename.endswith('.csv'):
            model_name = filename[:-4]  # Remove '.csv' from filename
            failed_files = []

            # Read the original CSV and collect failed files
            with open(os.path.join(results_dir, filename), 'r') as file:
                reader = csv.reader(file)
                next(reader)  # Skip header row
                for row in reader:
                    if len(row) > 2 and row[2] == 'failed':
                        failed_files.append((row[0], row[1]))  # Store both ID and filename

            # Write failed files to a new CSV in error_results directory
            error_file_path = os.path.join(error_dir, f"{model_name}-errors.csv")
            with open(error_file_path, 'w', newline='') as file:
                writer = csv.writer(file)
                writer.writerow(['ID', 'Failed File'])  # Updated header
                for id, failed_file in failed_files:
                    writer.writerow([id, failed_file])

            # Store the failed files for JSON output
            error_files[model_name] = failed_files
            all_failed_files.extend(failed_files)

    # Count occurrences of each failed file
    failed_file_counts = Counter(file for _, file in all_failed_files)

    return error_files, failed_file_counts, all_failed_files

def write_json(error_files):
    json_file_path = os.path.join(error_dir, 'error_files.json')
    with open(json_file_path, 'w') as json_file:
        json.dump(error_files, json_file, indent=2)

def write_summary_csv(failed_file_counts):
    summary_file_path = os.path.join(error_dir, 'failed_files_summary.csv')
    with open(summary_file_path, 'w', newline='') as file:
        writer = csv.writer(file)
        writer.writerow(['Failed File', 'Count'])  # Header
        for file, count in failed_file_counts.items():
            writer.writerow([file, count])

def write_detailed_summary_csv(all_failed_files):
    detailed_summary_path = os.path.join(error_dir, 'failed_files_detailed_summary.csv')
    with open(detailed_summary_path, 'w', newline='') as file:
        writer = csv.writer(file)
        writer.writerow(['ID', 'Failed File', 'Count'])  # Header
        id_file_count = {}
        for id, filename in all_failed_files:
            if (id, filename) not in id_file_count:
                id_file_count[(id, filename)] = 1
            else:
                id_file_count[(id, filename)] += 1
        
        for (id, filename), count in id_file_count.items():
            writer.writerow([id, filename, count])

def main():
    error_files, failed_file_counts, all_failed_files = process_csv_files()
    write_json(error_files)
    write_summary_csv(failed_file_counts)
    write_detailed_summary_csv(all_failed_files)
    print("Analysis complete. Results written to error_results directory.")
    print(f"Total unique failed files: {len(failed_file_counts)}")
    print(f"Total failures: {sum(failed_file_counts.values())}")

if __name__ == "__main__":
    main()