import os
import json
import argparse
from collections import defaultdict

# Define directories
base_dir = os.getcwd()  # Assuming we're in 'results/analysis/'
error_results_dir = os.path.join(base_dir, 'error_results')

def parse_dafny_errors(model_name):
    error_dir = os.path.join(error_results_dir, f"{model_name}__dafny_errors")
    errors = defaultdict(list)

    if not os.path.exists(error_dir):
        print(f"Warning: Dafny error directory not found for {model_name}")
        return errors

    for filename in os.listdir(error_dir):
        if filename.endswith('_verification.txt'):
            original_filename = filename.replace('_verification.txt', '.dfy')
            with open(os.path.join(error_dir, filename), 'r') as f:
                content = f.read()
                if "No errors found." not in content:
                    errors[original_filename] = content.strip().split('\n\n')

    return dict(errors)

def load_cheating_results(model_name):
    cheating_file = f'{model_name}__cheating_detection_results.json'
    if not os.path.exists(cheating_file):
        print(f"Warning: Cheating detection results not found for {model_name}")
        return {}

    with open(cheating_file, 'r') as f:
        return json.load(f)

def aggregate_results(model_names):
    aggregated_results = {}

    for model_name in model_names:
        dafny_errors = parse_dafny_errors(model_name)
        cheating_results = load_cheating_results(model_name)

        aggregated_results[model_name] = {
            'dafny_errors': dafny_errors,
            'cheating_detection': cheating_results,
            'summary': {
                'total_files': sum(len(files) for files in cheating_results.values()),
                'files_with_errors': len(dafny_errors),
                'files_with_altered_specs': len(cheating_results.get('altered_specs', [])),
                'files_with_trivial_verification': len(cheating_results.get('trivial_verification', [])),
                'files_with_both_issues': len(cheating_results.get('both_issues', [])),
                'files_without_issues': len(cheating_results.get('no_cheating', []))
            }
        }

    return aggregated_results

def main():
    parser = argparse.ArgumentParser(description="Aggregate Dafny errors and cheating detection results.")
    parser.add_argument("model_names", nargs='+', help="Names of the models to process (e.g., 'gpt-4o claude-3-opus')")
    args = parser.parse_args()

    print("Aggregating results...")
    results = aggregate_results(args.model_names)

    output_file = 'aggregated_results.json'
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=2)

    print(f"\nAggregated results saved to {output_file}")

    # Print summary for each model
    for model, data in results.items():
        print(f"\nSummary for {model}:")
        for key, value in data['summary'].items():
            print(f"  {key.replace('_', ' ').title()}: {value}")

if __name__ == "__main__":
    main()