import json
import os
import logging
from concurrent.futures import ThreadPoolExecutor, as_completed
from anthropic import Anthropic

# Set up logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

# Load API key from environment variable
API_KEY = os.getenv('ANTHROPIC_API_KEY')
if not API_KEY:
    logging.error("ANTHROPIC_API_KEY environment variable not set")
    exit(1)

# Initialize Anthropic client
client = Anthropic(api_key=API_KEY)

# Quality categories
QUALITY_CATEGORIES = ["poor", "medium", "good"]

def evaluate_code_quality(file_content):
    """
    Use Claude 3.5 Sonnet API to evaluate the code quality.
    """
    prompt = f"""Evaluate the following Dafny code for its overall quality. Be critical and somewhat harsh. Consider factors such as readability, modularity, use of appropriate Dafny features, and adherence to best practices. Categorize the code quality as one of: poor, medium, good.

Dafny Code:
{file_content}

Respond with only the category (poor, medium, or good)."""

    try:
        response = client.messages.create(
            model="claude-3-5-sonnet-20240620",
            max_tokens=10,
            messages=[
                {"role": "user", "content": prompt}
            ]
        )
        
        if not response.content:
            logging.warning(f"Empty response from API for file")
            return "medium"  # Default to medium if no response
        
        response_text = response.content[0].text.strip().lower()
        logging.info(f"API response for file: {response_text}")
        
        if response_text in QUALITY_CATEGORIES:
            return response_text
        else:
            logging.warning(f"Unexpected response: {response_text}")
            return "medium"  # Default to medium if unexpected response
    except Exception as e:
        logging.error(f"Error in API call: {str(e)}")
        return "medium"  # Default to medium if there's an API error

def process_file(filename):
    """
    Process a single Dafny file.
    """
    file_path = os.path.join('..', '..', 'DafnyBench', 'dataset', 'ground_truth', filename)
    try:
        with open(file_path, 'r') as f:
            file_content = f.read()
        quality = evaluate_code_quality(file_content)
        return {filename: quality}
    except Exception as e:
        logging.error(f"Error processing file {filename}: {str(e)}")
        return {filename: "error"}

def main():
    try:
        # Get list of Dafny files
        dafny_dir = os.path.join('..', '..', 'DafnyBench', 'dataset', 'ground_truth')
        dafny_files = [f for f in os.listdir(dafny_dir) if f.endswith('.dfy')]

        results = {}
        with ThreadPoolExecutor(max_workers=5) as executor:
            future_to_file = {executor.submit(process_file, filename): filename for filename in dafny_files}
            for future in as_completed(future_to_file):
                filename = future_to_file[future]
                try:
                    result = future.result()
                    results.update(result)
                except Exception as exc:
                    logging.error(f'{filename} generated an exception: {exc}')

        # Save the results
        with open('dafny_code_quality.json', 'w') as f:
            json.dump(results, f, indent=2)
        
        logging.info("Processing completed successfully. Results saved to 'dafny_code_quality.json'")
    except Exception as e:
        logging.error(f"An error occurred in the main function: {str(e)}")

if __name__ == "__main__":
    main()