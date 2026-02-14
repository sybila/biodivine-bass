import sys
import os
import csv

def process_benchmark_folder(folder_path):
    results_file = os.path.join(folder_path, "__results.csv")
    if not os.path.exists(results_file):
        print(f"Error: {results_file} not found.")
        return

    # Temporary list to store updated rows
    updated_rows = []
    header = None
    
    killed_count = 0

    with open(results_file, mode='r', newline='') as csvfile:
        reader = csv.DictReader(csvfile)
        header = reader.fieldnames
        for row in reader:
            instance = row['Instance']
            log_file = os.path.join(folder_path, f"{instance}.log")
            
            is_killed = False
            if os.path.exists(log_file):
                try:
                    with open(log_file, 'r', errors='ignore') as f:
                        if 'Killed' in f.read():
                            is_killed = True
                except Exception as e:
                    print(f"Warning: Could not read log file {log_file}: {e}")
            
            if is_killed:
                row['Status'] = 'ERROR'
                # Optionally, we might want to keep the time or set it to something else.
                # The user said "assigned an error instead of a successful time", 
                # which implies Status should be ERROR.
                killed_count += 1
            
            updated_rows.append(row)

    # Write back to __results.csv
    with open(results_file, mode='w', newline='') as csvfile:
        writer = csv.DictWriter(csvfile, fieldnames=header)
        writer.writeheader()
        writer.writerows(updated_rows)

    print(f"Processed {len(updated_rows)} entries. Updated {killed_count} 'Killed' entries to ERROR.")

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python fix_killed_results.py <benchmark_folder>")
        sys.exit(1)
    
    target_folder = sys.argv[1]
    process_benchmark_folder(target_folder)
