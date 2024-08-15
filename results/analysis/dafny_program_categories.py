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

# Topic categories
TOPIC_CATEGORIES = [
    "CS Problem",
    "Machine Learning/Data Science",
    "Math Topic",
    "Combination",
    "Application"
]

def categorize_program(file_content, filename):
    """
    Use Claude 3.5 Sonnet API to categorize the Dafny program.
    """
    prompt = f"""Categorize the following Dafny program into one of these categories:
1. CS Problem (Examples: Array processing, Search, sorting, string processing, common algorithm implementation practice, map objects, dafny practice for generic simply programs)
2. Machine Learning/Data Science (Example: gradient descent)
3. Math Topic (Examples: gaussian, arithmetic operators, set operations, absolute value, logic)
4. Combination (Combination of any other categories)
5. Application (Example: Specific program for a unique topic, like a car park, boat rescue, or ethereum)

Dafny Program (filename: {filename}):
{file_content}

Respond with only the category number."""

    try:
        response = client.messages.create(
            model="claude-3-5-sonnet-20240620",
            max_tokens=10,
            messages=[
                {"role": "user", "content": prompt}
            ]
        )
        
        if not response.content:
            logging.warning(f"Empty response from API for file: {filename}")
            return "Unknown"
        
        response_text = response.content[0].text.strip()
        logging.info(f"API response for file {filename}: {response_text}")
        
        try:
            category_num = int(response_text)
            return TOPIC_CATEGORIES[category_num - 1] if 1 <= category_num <= 5 else "Unknown"
        except ValueError:
            logging.warning(f"Unexpected response format for file {filename}: {response_text}")
            return "Unknown"
    except Exception as e:
        logging.error(f"Error in API call for file {filename}: {str(e)}")
        return "Unknown"

def process_file(filename):
    """
    Process a single Dafny file.
    """
    file_path = os.path.join('..', '..', 'DafnyBench', 'dataset', 'ground_truth', filename)
    try:
        with open(file_path, 'r') as f:
            file_content = f.read()
        category = categorize_program(file_content, filename)
        return {filename: category}
    except Exception as e:
        logging.error(f"Error processing file {filename}: {str(e)}")
        return {filename: "Error"}

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
        with open('dafny_program_categories.json', 'w') as f:
            json.dump(results, f, indent=2)
        
        logging.info("Processing completed successfully. Results saved to 'dafny_program_categories.json'")
    except Exception as e:
        logging.error(f"An error occurred in the main function: {str(e)}")

if __name__ == "__main__":
    main()