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

def load_timeout_info(model_name):
    timeout_file = f'{model_name}__timeout_info.json'
    if not os.path.exists(timeout_file):
        print(f"Warning: Timeout information not found for {model_name}")
        return []

    with open(timeout_file, 'r') as f:
        return json.load(f).get('timeouts', [])

def load_verification_summary(model_name):
    summary_file = f'{model_name}__dafny_verification_summary.json'
    if not os.path.exists(summary_file):
        print(f"Warning: Verification summary not found for {model_name}")
        return {}

    with open(summary_file, 'r') as f:
        return json.load(f)

def aggregate_results(model_names):
    aggregated_results = {}

    for model_name in model_names:
        dafny_errors = parse_dafny_errors(model_name)
        cheating_results = load_cheating_results(model_name)
        timeout_info = load_timeout_info(model_name)
        verification_summary = load_verification_summary(model_name)

        total_files = len(verification_summary.get(model_name, []))
        files_with_errors = sum(1 for r in verification_summary.get(model_name, []) if r['error_count'] > 0)

        aggregated_results[model_name] = {
            'dafny_errors': dafny_errors,
            'cheating_detection': cheating_results,
            'timeouts': timeout_info,
            'verification_summary': verification_summary,
            'summary': {
                'total_files': total_files,
                'files_with_errors': files_with_errors,
                'files_with_timeouts': len(timeout_info),
                'files_with_altered_specs': len(cheating_results.get('altered_specs', [])),
                'files_with_trivial_verification': len(cheating_results.get('trivial_verification', [])),
                'files_with_both_issues': len(cheating_results.get('both_issues', [])),
                'files_without_issues': len(cheating_results.get('no_cheating', [])),
                'files_verified_successfully': total_files - files_with_errors - len(timeout_info)
            }
        }

    return aggregated_results

def main():
    parser = argparse.ArgumentParser(description="Aggregate Dafny errors, cheating detection results, and timeout information.")
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