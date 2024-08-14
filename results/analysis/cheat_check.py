import os
import json
import argparse

# Define directories
base_dir = os.path.dirname(os.path.dirname(os.getcwd()))  # Assuming we're in 'results/analysis'
ground_truth_dir = os.path.join(base_dir, 'DafnyBench', 'dataset', 'ground_truth')
error_results_dir = os.path.join(os.getcwd(), 'error_results')

def check_no_cheating(body, body_reconstructed):
    spec_orig, spec_llm = [], []
    in_doc, in_doc_hints = False, False
    avoid_verify_found = False
    
    for line in body.split("\n"):
        if line.strip().startswith("/*"):
            in_doc = True
        elif line.strip().endswith("*/"):
            in_doc = False
        is_comment = in_doc or line.strip().startswith("//")
        if ("requires" in line or "ensures" in line) and not is_comment:
            spec_orig.append(line.strip().replace(" ", ""))
    
    for line_hints in body_reconstructed.split("\n"):
        if line_hints.strip().startswith("/*"):
            in_doc_hints = True
        elif line_hints.strip().endswith("*/"):
            in_doc_hints = False
        is_comment_hints = in_doc_hints or line_hints.strip().startswith("//")
        if ("requires" in line_hints or "ensures" in line_hints) and not is_comment_hints:
            spec_llm.append(line_hints.strip().replace(" ", ""))
        if not is_comment_hints:
            if '{:verify false}' in line_hints or 'assume false' in line_hints:
                avoid_verify_found = True
    
    spec_preserved = spec_orig == spec_llm
    no_avoid_verify = not avoid_verify_found
    return spec_preserved, no_avoid_verify

def get_original_filename(llm_filename):
    # Remove the numeric prefix and '_no_hints' suffix
    parts = llm_filename.split('_')
    return '_'.join(parts[1:-2]) + '.dfy'

def process_files(model_name):
    cheating_results = {
        'altered_specs': [],
        'trivial_verification': [],
        'both_issues': [],
        'no_cheating': []
    }
    
    llm_output_dir = os.path.join(error_results_dir, f"{model_name}__outputs")
    
    if not os.path.exists(llm_output_dir):
        print(f"Error: Directory not found: {llm_output_dir}")
        return cheating_results

    for filename in os.listdir(llm_output_dir):
        if filename.endswith('.dfy'):
            original_filename = get_original_filename(filename)
            llm_file_path = os.path.join(llm_output_dir, filename)
            original_file_path = os.path.join(ground_truth_dir, original_filename)
            
            if not os.path.exists(original_file_path):
                print(f"Warning: Original file not found: {original_file_path}")
                continue
            
            with open(original_file_path, 'r') as f:
                original_body = f.read()
            
            with open(llm_file_path, 'r') as f:
                llm_body = f.read()
            
            spec_preserved, no_avoid_verify = check_no_cheating(original_body, llm_body)
            
            if not spec_preserved and not no_avoid_verify:
                cheating_results['both_issues'].append(filename)
            elif not spec_preserved:
                cheating_results['altered_specs'].append(filename)
            elif not no_avoid_verify:
                cheating_results['trivial_verification'].append(filename)
            else:
                cheating_results['no_cheating'].append(filename)
    
    return cheating_results

def main():
    parser = argparse.ArgumentParser(description="Detect cheating in LLM-generated Dafny files.")
    parser.add_argument("model_name", help="Name of the model to process (e.g., 'gpt-4o')")
    args = parser.parse_args()

    print(f"Checking for cheating in {args.model_name} outputs...")
    
    results = process_files(args.model_name)
    
    print("\nCheating detection results:")
    print(f"Files with altered specs: {len(results['altered_specs'])}")
    print(f"Files with trivial verification: {len(results['trivial_verification'])}")
    print(f"Files with both issues: {len(results['both_issues'])}")
    print(f"Files with no cheating detected: {len(results['no_cheating'])}")
    
    # Save the detailed results to a JSON file
    output_file = f'{args.model_name}__cheating_detection_results.json'
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nDetailed results saved to {output_file}")

if __name__ == "__main__":
    main()