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

# Error categories mapping
ERROR_CATEGORIES = {
    1: "code_logic_error",
    2: "verification_logic_error",
    3: "syntax_issue",
    4: "type_error",
    5: "resolution_error",
    6: "other"
}

def categorize_error(error):
    """
    Use Claude 3.5 Sonnet API to categorize the error.
    """
    prompt = f"""Categorize the following Dafny error into one of these categories:
1. code logic errors (examples: "index out of range", "lower bound / upper bound", "might be uninitialized", "target object might be null", "'this' can only be used to assign to its fields")
2. verification logic error (examples: "could not be proved", "assertion might not hold", "decreases expression might not decrease", "cannot prove termination", "decrease expression must be bounded below", "violation of ... ", "call to possibly non-terminating...", "cannot establish existence of ... values that satisfy...")
3. syntax issue (examples: "invalid ...", "lbrace/rbrace expected", "lbracket/rbracket expected", "unresolved identifier", "must use refining ... notation", "semicolon expected", "*paren expected", "symbol not expected")
4. type error (examples: "Value does not satisfy the subset constraints of 'nat'", "member does not exist in datatype", "array assignment must denote array element (found seq<...,)", "argument to ... must be a ...", "incorrect type", "incompatible with expected type", "type * does not have member *")
5. resolution error (examples: "Boogie had ... resolution errors")
6. other (fails to meet other categorization)

Error: {error}

Respond with only the category number."""

    try:
        response = client.messages.create(
            model="claude-3-5-sonnet-20240620",
            max_tokens=10,  # Increased to allow for potential unexpected responses
            messages=[
                {"role": "user", "content": prompt}
            ]
        )
        
        if not response.content:
            logging.warning(f"Empty response from API for error: {error[:100]}...")
            return "other"
        
        response_text = response.content[0].text.strip()
        logging.info(f"API response for error '{error[:100]}...': {response_text}")
        
        try:
            category_num = int(response_text)
            return ERROR_CATEGORIES.get(category_num, "other")
        except ValueError:
            logging.warning(f"Unexpected response format: {response_text}")
            return "other"
    except Exception as e:
        logging.error(f"Error in API call: {str(e)}")
        return "other"  # Default to "other" if there's an API error

def process_file(filename, errors, model):
    """
    Process errors for a single file.
    """
    categorized_errors = {category: 0 for category in ERROR_CATEGORIES.values()}
    for error in errors:
        category = categorize_error(error)
        categorized_errors[category] += 1
    return {filename: categorized_errors}

def process_model(model, data):
    """
    Process all files for a single model.
    """
    results = {}
    with ThreadPoolExecutor(max_workers=5) as executor:
        future_to_file = {executor.submit(process_file, filename, errors, model): filename 
                          for filename, errors in data['dafny_errors'].items()}
        for future in as_completed(future_to_file):
            filename = future_to_file[future]
            try:
                result = future.result()
                results.update(result)
            except Exception as exc:
                logging.error(f'{filename} generated an exception: {exc}')
    return {model: results}

def main():
    try:
        # Load the JSON file
        with open('aggregated_results.json', 'r') as f:
            data = json.load(f)

        # Process each model
        results = {}
        for model, model_data in data.items():
            results.update(process_model(model, model_data))

        # Save the results
        with open('categorized_errors.json', 'w') as f:
            json.dump(results, f, indent=2)
        
        logging.info("Processing completed successfully. Results saved to 'categorized_errors.json'")
    except Exception as e:
        logging.error(f"An error occurred in the main function: {str(e)}")

if __name__ == "__main__":
    main()