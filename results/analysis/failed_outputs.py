import os
import json

# Define directories
base_dir = os.path.dirname(os.getcwd())  # Parent directory of 'analysis'
reconstructed_dir = os.path.join(base_dir, 'reconstructed_files')
error_results_dir = os.path.join(os.getcwd(), 'error_results')
error_file_path = os.path.join(error_results_dir, 'error_files.json')

def load_error_files():
    with open(error_file_path, 'r') as f:
        return json.load(f)

def ensure_dir(directory):
    if not os.path.exists(directory):
        os.makedirs(directory)

def process_reconstructed_files(error_files):
    matching_errors = {}

    for filename in os.listdir(reconstructed_dir):
        if filename.endswith('_outputs.json'):
            model_name = filename[:-12]  # Remove '_outputs.json'
            file_path = os.path.join(reconstructed_dir, filename)
            
            with open(file_path, 'r') as f:
                reconstructed_data = json.load(f)

            # Find the corresponding key in error_files
            error_key = next((key for key in error_files.keys() if model_name in key), None)

            if error_key:
                matching_errors[model_name] = []
                model_output_dir = os.path.join(error_results_dir, f"{model_name}_outputs")
                ensure_dir(model_output_dir)

                for id, _ in error_files[error_key]:
                    if id in reconstructed_data:
                        matching_errors[model_name].append(id)
                        output_content = reconstructed_data[id]["llm_output"]
                        output_filename = f"{id}_{reconstructed_data[id]['test_file']}"
                        output_path = os.path.join(model_output_dir, output_filename)
                        
                        with open(output_path, 'w') as out_file:
                            out_file.write(output_content)

    return matching_errors

def main():
    error_files = load_error_files()
    matching_errors = process_reconstructed_files(error_files)

    print("Matching errors found and processed:")
    for model, errors in matching_errors.items():
        print(f"{model}: {len(errors)} matching errors")
        print(f"IDs: {errors[:5]}{'...' if len(errors) > 5 else ''}")
        print(f"Outputs saved in: {os.path.join(error_results_dir, f'{model}_outputs')}")
        print()

    # Save the summary to a JSON file in the current directory (analysis/)
    output_file = 'matching_errors_summary.json'
    with open(output_file, 'w') as f:
        json.dump(matching_errors, f, indent=2)
    print(f"Summary of matching errors saved to {output_file}")

if __name__ == "__main__":
    main()