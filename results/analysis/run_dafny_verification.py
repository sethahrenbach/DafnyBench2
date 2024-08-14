import os
import subprocess
import json
import re
import sys
import argparse

# Define directories
base_dir = os.getcwd()  # Assuming we're in the 'analysis' directory
error_results_dir = os.path.join(base_dir, 'error_results')

def ensure_dir(directory):
    if not os.path.exists(directory):
        os.makedirs(directory)

def run_dafny_verification(file_path):
    try:
        print(f"  Verifying: {os.path.basename(file_path)}")
        result = subprocess.run(['dafny', 'verify', file_path], 
                                capture_output=True, text=True, timeout=300)
        return result.returncode, result.stdout, result.stderr
    except subprocess.TimeoutExpired:
        print(f"  Timeout occurred for {os.path.basename(file_path)}")
        return -1, "", "Verification timed out after 5 minutes"
    except Exception as e:
        print(f"  Error occurred while verifying {os.path.basename(file_path)}: {e}")
        return -1, "", str(e)

def extract_errors(output, filename):
    errors = []
    lines = output.split('\n')
    error_pattern = re.compile(r'(.*?)\((\d+),(\d+)\): (Error|Warning): (.+)')
    in_error_block = False
    current_error = []
    
    for line in lines:
        if not in_error_block:
            match = error_pattern.search(line)
            if match:
                file_path, line_num, col_num, error_type, error_message = match.groups()
                if filename in file_path and error_type == "Error":
                    current_error = [line]
                    in_error_block = True
        else:
            if line.strip() == "":
                if current_error:
                    errors.append('\n'.join(current_error))
                    current_error = []
                in_error_block = False
            else:
                current_error.append(line)
    
    if current_error:
        errors.append('\n'.join(current_error))
    
    return errors

def process_dafny_files(model_name):
    verification_results = {}
    timeouts = []
    
    input_dir = os.path.join(error_results_dir, f"{model_name}__outputs")
    output_dir = os.path.join(error_results_dir, f"{model_name}__dafny_errors")
    
    if not os.path.exists(input_dir):
        print(f"Error: Directory not found: {input_dir}")
        return verification_results, timeouts

    print(f"Processing model: {model_name}")
    ensure_dir(output_dir)
    
    verification_results[model_name] = []

    dfy_files = [f for f in os.listdir(input_dir) if f.endswith('.dfy')]
    if not dfy_files:
        print(f"  No .dfy files found in {input_dir}")
        return verification_results, timeouts

    for filename in dfy_files:
        input_path = os.path.join(input_dir, filename)
        output_path = os.path.join(output_dir, f"{filename[:-4]}_verification.txt")
        
        returncode, stdout, stderr = run_dafny_verification(input_path)
        errors = extract_errors(stdout + stderr, filename)
        
        with open(output_path, 'w') as f:
            if errors:
                f.write('\n\n'.join(errors))
            else:
                f.write("No errors found.")
        
        result = {
            'file': filename,
            'returncode': returncode,
            'error_count': len(errors),
            'output_file': os.path.basename(output_path)
        }
        verification_results[model_name].append(result)
        
        if returncode == -1:  # Timeout case
            timeouts.append(filename)

    print(f"  Processed {len(dfy_files)} files for {model_name}")

    return verification_results, timeouts

def save_timeout_info(model_name, timeouts):
    timeout_file = f'{model_name}__timeout_info.json'
    with open(timeout_file, 'w') as f:
        json.dump({"timeouts": timeouts}, f, indent=2)
    print(f"Timeout information saved to {timeout_file}")

def main():
    parser = argparse.ArgumentParser(description="Run Dafny verification on a specific model's output.")
    parser.add_argument("model_name", help="Name of the model to process (e.g., 'gpt-4o')")
    args = parser.parse_args()

    print("Starting Dafny verification process...")
    
    try:
        # Check if Dafny is installed
        subprocess.run(['dafny', '--version'], capture_output=True, check=True)
    except subprocess.CalledProcessError:
        print("Error: Dafny is not installed or not in the system PATH.")
        print("Please install Dafny and make sure it's accessible from the command line.")
        sys.exit(1)
    except FileNotFoundError:
        print("Error: Dafny command not found.")
        print("Please install Dafny and make sure it's accessible from the command line.")
        sys.exit(1)

    verification_results, timeouts = process_dafny_files(args.model_name)

    if not verification_results:
        print(f"No results generated for model: {args.model_name}")
        return

    print("\nDafny verification completed:")
    for model, results in verification_results.items():
        print(f"{model}: {len(results)} files verified")
        error_count = sum(r['error_count'] for r in results)
        print(f"  Files with errors: {sum(1 for r in results if r['error_count'] > 0)}")
        print(f"  Total errors found: {error_count}")
        print(f"  Files with timeouts: {len(timeouts)}")
        print(f"  Results stored in: {os.path.join(error_results_dir, f'{model}__dafny_errors')}")

    # Save the summary to a JSON file
    output_file = f'{args.model_name}__dafny_verification_summary.json'
    with open(output_file, 'w') as f:
        json.dump(verification_results, f, indent=2)
    print(f"Summary of Dafny verification results saved to {output_file}")

    # Save timeout information
    save_timeout_info(args.model_name, timeouts)

if __name__ == "__main__":
    main()