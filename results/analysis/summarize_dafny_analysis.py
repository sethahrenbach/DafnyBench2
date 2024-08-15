import json
import os
from collections import Counter, defaultdict

def load_json(filename):
    with open(filename, 'r') as f:
        return json.load(f)

def summarize_data(quality_data, category_data):
    quality_counter = Counter(quality_data.values())
    category_counter = Counter(category_data.values())
    
    quality_category_matrix = defaultdict(lambda: defaultdict(int))
    for filename, quality in quality_data.items():
        if filename in category_data:
            category = category_data[filename]
            quality_category_matrix[quality][category] += 1
    
    return quality_counter, category_counter, quality_category_matrix

def create_summary_dict(quality_counter, category_counter, quality_category_matrix):
    total_files = sum(quality_counter.values())
    
    summary = {
        "total_files": total_files,
        "quality_distribution": {
            quality: {
                "count": count,
                "percentage": (count / total_files) * 100
            } for quality, count in quality_counter.items()
        },
        "category_distribution": {
            category: {
                "count": count,
                "percentage": (count / total_files) * 100
            } for category, count in category_counter.items()
        },
        "quality_category_matrix": {
            quality: {category: count for category, count in categories.items()}
            for quality, categories in quality_category_matrix.items()
        },
        "category_quality_distribution": {}
    }
    
    for category in ["Basic Algorithm", "Math Topic", "Application", "Combination"]:
        category_total = sum(quality_category_matrix[quality][category] for quality in ["good", "medium", "poor"])
        summary["category_quality_distribution"][category] = {
            quality: {
                "count": quality_category_matrix[quality][category],
                "percentage": (quality_category_matrix[quality][category] / category_total) * 100 if category_total > 0 else 0
            } for quality in ["good", "medium", "poor"]
        }
    
    return summary

def main():
    current_dir = os.path.dirname(os.path.abspath(__file__))
    quality_file = os.path.join(current_dir, 'dafny_code_quality.json')
    category_file = os.path.join(current_dir, 'dafny_program_categoriesv0.json')
    
    try:
        quality_data = load_json(quality_file)
        category_data = load_json(category_file)
        
        quality_counter, category_counter, quality_category_matrix = summarize_data(quality_data, category_data)
        
        summary_dict = create_summary_dict(quality_counter, category_counter, quality_category_matrix)
        
        # Save the summary to a JSON file
        with open('dafny_analysis_summary.json', 'w') as f:
            json.dump(summary_dict, f, indent=2)
        
        print("Summary has been saved to 'dafny_analysis_summary.json'")
        
    except FileNotFoundError as e:
        print(f"Error: {e}. Please make sure both JSON files are in the current directory.")
    except json.JSONDecodeError as e:
        print(f"Error decoding JSON: {e}. Please check the format of the JSON files.")
    except Exception as e:
        print(f"An unexpected error occurred: {e}")

if __name__ == "__main__":
    main()