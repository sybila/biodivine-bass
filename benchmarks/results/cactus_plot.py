import os
import pandas as pd
import matplotlib.pyplot as plt
import argparse
import glob

# Configuration for tool labels and colors to ensure consistency across plots.
# You can modify this dictionary to add new tools or change existing ones.
TOOL_CONFIG = {
    "bass": {"label": "BAss", "color": "#1f77b4"},      # Blue
    "aeon": {"label": "aeon", "color": "#ff7f0e"},      # Orange
    "biolqm": {"label": "bioLQM", "color": "#2ca02c"},  # Green
    "bsaf": {"label": "H.E.", "color": "#d62728"},      # Red
    "yadf": {"label": "yadf", "color": "#9467bd"},      # Purple
    "k_adf": {"label": "k++ADF", "color": "#8c564b"},    # Brown
    "goDiamond": {"label": "goDiamond", "color": "#e377c2"}, # Pink
    "adf_obdd": {"label": "adf-bdd", "color": "#17becf"},   # Gray
    "fasp": {"label": "fASP", "color": "#bcbd22"},   # Gray
    "tsconj": {"label": "ts-conj", "color": "#98df8a"},   # Gray
    "mpbn": {"label": "mpbn", "color": "#7f7f7f"},   # Gray
}

def create_cactus_plot(directory, output_file=None, timeout=1200):
    """
    Creates a cactus plot from CSV files in the given directory.
    Each CSV file is expected to have columns: Instance, Status, Runtime_sec, ...
    """
    csv_files = glob.glob(os.path.join(directory, "*.csv"))
    if not csv_files:
        print(f"No CSV files found in {directory}")
        return

    # Load excluded instances
    exclude_path = os.path.join(os.path.dirname(__file__), "exclude.txt")
    excluded_instances = set()
    if os.path.exists(exclude_path):
        with open(exclude_path, 'r') as f:
            # Load and strip extensions for comparison
            excluded_instances = {os.path.splitext(line.strip())[0] for line in f if line.strip()}
        print(f"Loaded {len(excluded_instances)} excluded instances from {exclude_path}")

    plt.figure(figsize=(10, 6))
    
    # Track max instances to set x-axis limit
    max_solved = 0
    
    # Default color cycle for tools not in TOOL_CONFIG
    default_colors = plt.cm.tab10.colors
    default_color_idx = 0

    for csv_file in sorted(csv_files):
        tool_id = os.path.splitext(os.path.basename(csv_file))[0]
        if tool_id == "summary": # Skip summary files if any
            continue
            
        try:
            df = pd.read_csv(csv_file)
            
            # Remove excluded instances
            if not df.empty and 'Instance' in df.columns:
                # Compare without extensions
                df = df[~df['Instance'].apply(lambda x: os.path.splitext(str(x))[0]).isin(excluded_instances)]

            # Filter for successful runs and sort by runtime
            # Assuming 'OK' status means success. 
            solved_df = df[df['Status'] == 'OK'].copy()
            
            if solved_df.empty:
                print(f"No solved instances for {tool_id}")
                continue
                
            runtimes = sorted(solved_df['Runtime_sec'].values)
            # Ensure runtimes are at least a small positive value for log scale
            runtimes = [max(r, 0.001) for r in runtimes]
            
            n_solved = len(runtimes)
            max_solved = max(max_solved, n_solved)
            
            # Get label and color from config or use defaults
            if tool_id in TOOL_CONFIG:
                label = f"{TOOL_CONFIG[tool_id]['label']} ({n_solved})"
                color = TOOL_CONFIG[tool_id]['color']
            else:
                label = f"{tool_id} ({n_solved})"
                color = default_colors[default_color_idx % len(default_colors)]
                default_color_idx += 1

            plt.plot(range(1, n_solved + 1), runtimes, label=label, color=color, linewidth=2)
            
        except Exception as e:
            print(f"Error processing {csv_file}: {e}")

    plt.yscale('log')
    plt.xlabel('Number of instances solved')
    plt.ylabel('Runtime (seconds)')
    plt.title(f'Cactus Plot - {os.path.basename(directory.strip("/"))}')
    plt.grid(True, which="both", ls="-", alpha=0.3)
    
    if timeout:
        plt.axhline(y=timeout, color='black', linestyle='--', alpha=0.5, label=f'Timeout ({timeout}s)')

    plt.legend(bbox_to_anchor=(1.05, 1), loc='upper left')
    plt.tight_layout()

    if output_file:
        plt.savefig(output_file)
        print(f"Plot saved to {output_file}")
    else:
        plt.show()

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Generate a cactus plot from benchmark results.')
    parser.add_argument('directory', type=str, help='Directory containing result CSV files (e.g., 2v, adm)')
    parser.add_argument('--output', type=str, default=None, help='Output image file path')
    parser.add_argument('--timeout', type=float, default=1200, help='Timeout value to show on plot')

    args = parser.parse_args()
    
    if not args.output:
        dir_name = os.path.basename(args.directory.strip("/"))
        args.output = f"cactus_{dir_name}.png"
        
    create_cactus_plot(args.directory, args.output, args.timeout)
