import json
import logging
from collections import defaultdict

# Set up logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

def summarize_errors():
    try:
        # Load the categorized errors JSON file
        with open('categorized_errors.json', 'r') as f:
            data = json.load(f)

        summary = {}

        for model, files in data.items():
            model_summary = defaultdict(int)
            total_errors = 0

            # Sum up errors across all files for this model
            for file_errors in files.values():
                for category, count in file_errors.items():
                    model_summary[category] += count
                    total_errors += count

            # Calculate percentages
            percentages = {
                category: (count / total_errors) * 100 if total_errors > 0 else 0
                for category, count in model_summary.items()
            }

            summary[model] = {
                "total_errors": total_errors,
                "error_counts": dict(model_summary),
                "error_percentages": percentages
            }

        # Save the summary to a new JSON file
        with open('error_summary.json', 'w') as f:
            json.dump(summary, f, indent=2)

        logging.info("Summary completed successfully. Results saved to 'error_summary.json'")

        # Print a human-readable summary to console
        print("\nSummary of errors for each model:")
        for model, data in summary.items():
            print(f"\n{model}:")
            print(f"  Total errors: {data['total_errors']}")
            print("  Error counts:")
            for category, count in data['error_counts'].items():
                print(f"    {category}: {count}")
            print("  Error percentages:")
            for category, percentage in data['error_percentages'].items():
                print(f"    {category}: {percentage:.2f}%")

    except Exception as e:
        logging.error(f"An error occurred: {str(e)}")

if __name__ == "__main__":
    summarize_errors()