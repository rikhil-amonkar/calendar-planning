import os
import json
import shutil
from collections import defaultdict

def count_constraints(constraint_dict):
    """
    Count the total number of constraints in a constraint dictionary
    """
    total = 0
    for key in constraint_dict:
        # Skip the input_query and optimization fields
        if key in ["input_query", "optimization"]:
            continue
        
        # Get the constraint value
        constraint_value = constraint_dict[key]
        
        # Handle different types of constraint values
        if isinstance(constraint_value, (list, dict)):
            total += len(constraint_value)
        elif isinstance(constraint_value, (int, float)):
            # If it's a number, count it as 1 constraint
            total += 1
        else:
            # For other types (strings, etc.), count as 1 constraint
            total += 1
    return total

def process_json_file(file_path):
    """
    Process a single JSON file and return its constraint count
    """
    with open(file_path, 'r') as f:
        data = json.load(f)
    
    # The structure is always {filename: constraints}, so we get the first value
    constraint_data = next(iter(data.values()))
    return count_constraints(constraint_data)

def load_model_results(model_results_path):
    """
    Load the model results JSON file and create a dictionary mapping example IDs to their results
    """
    with open(model_results_path, 'r') as f:
        data = json.load(f)
    
    results_dict = {}
    for entry in data.get("0shot", []):
        example_id = entry["count"]
        results_dict[example_id] = {
            "final": entry["final_program_time"],
            "expected": entry["expected_time"],
            "is_correct": (entry["final_program_time"]["day"] == entry["expected_time"]["day"] and
                          entry["final_program_time"]["start_time"] == entry["expected_time"]["start_time"] and
                          entry["final_program_time"]["end_time"] == entry["expected_time"]["end_time"])
        }
    return results_dict

def categorize_files(file_constraints, num_groups=5):
    """
    Categorize files into difficulty groups based on constraint counts
    Returns a dictionary of {group_name: [file_paths]}
    """
    # Sort files by constraint count (descending)
    sorted_files = sorted(file_constraints.items(), key=lambda x: x[1], reverse=True)
    total_files = len(sorted_files)
    
    # Calculate how many files per group (approximately)
    files_per_group = total_files // num_groups
    
    categories = {
        "80-100%": [],
        "60-80%": [],
        "40-60%": [],
        "20-40%": [],
        "0-20%": []
    }
    
    for i, (file_path, count) in enumerate(sorted_files):
        if i < files_per_group:
            categories["80-100%"].append((file_path, count))
        elif i < 2 * files_per_group:
            categories["60-80%"].append((file_path, count))
        elif i < 3 * files_per_group:
            categories["40-60%"].append((file_path, count))
        elif i < 4 * files_per_group:
            categories["20-40%"].append((file_path, count))
        else:
            categories["0-20%"].append((file_path, count))
    
    return categories

def create_output_folders(output_dir, categories):
    """
    Create output folders and copy files to their respective categories
    """
    # Create the main output directory if it doesn't exist
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)
    
    # Create category subdirectories
    for category in categories:
        category_dir = os.path.join(output_dir, category)
        if not os.path.exists(category_dir):
            os.makedirs(category_dir)
        
        # Copy files to their category directory
        for file_path, _ in categories[category]:
            file_name = os.path.basename(file_path)
            dest_path = os.path.join(category_dir, file_name)
            shutil.copy2(file_path, dest_path)

def generate_summary_file(summary_path, categories, model_results):
    """
    Generate a summary text file showing all constraints ranked by difficulty with accuracy info
    """
    category_stats = {
        "80-100%": {"correct": 0, "total": 0},
        "60-80%": {"correct": 0, "total": 0},
        "40-60%": {"correct": 0, "total": 0},
        "20-40%": {"correct": 0, "total": 0},
        "0-20%": {"correct": 0, "total": 0}
    }
    
    with open(summary_path, 'w') as f:
        f.write("Constraint Files Ranked by Difficulty with Model Accuracy\n")
        f.write("=======================================================\n")
        
        for category in ["80-100%", "60-80%", "40-60%", "20-40%", "0-20%"]:
            f.write(f"\n=============== {category} Most Constrained ===============\n")
            
            # Sort files in this category by constraint count (descending)
            sorted_files = sorted(categories[category], key=lambda x: x[1], reverse=True)
            
            for file_path, count in sorted_files:
                file_name = os.path.basename(file_path)
                # Extract the example ID from the filename (assuming format like "calendar_scheduling_example_XXX.json")
                example_id = file_name.replace('.json', '')
                
                # Check if this example exists in the model results
                accuracy_status = "NOT FOUND"
                if example_id in model_results:
                    category_stats[category]["total"] += 1
                    if model_results[example_id]["is_correct"]:
                        accuracy_status = "CORRECT"
                        category_stats[category]["correct"] += 1
                    else:
                        accuracy_status = "INCORRECT"
                
                f.write(f"{file_name}: {count} constraints - {accuracy_status}\n")
        
        # Add summary statistics at the end
        f.write("\n\n=============== Accuracy Summary ===============\n")
        for category in ["80-100%", "60-80%", "40-60%", "20-40%", "0-20%"]:
            total = category_stats[category]["total"]
            correct = category_stats[category]["correct"]
            accuracy = (correct / total * 100) if total > 0 else 0
            f.write(f"{category}: {correct}/{total} correct ({accuracy:.1f}%)\n")

def main(input_folder, output_folder, summary_file_path, model_results_path):
    """
    Main function to process all JSON files in the input folder
    """
    # Dictionary to store file paths and their constraint counts
    file_constraints = {}
    
    # Load model results
    model_results = load_model_results(model_results_path)
    
    # Process all JSON files in the input folder
    for file_name in os.listdir(input_folder):
        if file_name.endswith('.json'):
            file_path = os.path.join(input_folder, file_name)
            try:
                constraint_count = process_json_file(file_path)
                file_constraints[file_path] = constraint_count
            except (json.JSONDecodeError, KeyError) as e:
                print(f"Error processing {file_name}: {e}")
                continue
    
    # Categorize files into difficulty groups
    categories = categorize_files(file_constraints)
    
    # Create output folders with categorized files
    create_output_folders(output_folder, categories)
    
    # Generate the summary text file with accuracy information
    generate_summary_file(summary_file_path, categories, model_results)
    
    print(f"Processing complete. Results saved to {output_folder}")
    print(f"Summary file created at {summary_file_path}")

if __name__ == "__main__":
    # Configuration - change these paths as needed
    INPUT_FOLDER = "constraint_satisfaction/calendar"  # Folder containing the JSON files
    OUTPUT_FOLDER = "bucketed_constraints/bucketed_result_groups/calendar"  # Where to save the categorized files
    SUMMARY_FILE = "bucketed_constraints/constraint_summary_calendar_2.txt"  # Path for the summary text file
    MODEL_RESULTS_PATH = "calendar_scheduling/100_random_0shot_text_outputs_new/O3-M-25-01-31_forceJSON_text_calendar_results.json"  # Path to the model results JSON file
    
    # Run the program
    main(INPUT_FOLDER, OUTPUT_FOLDER, SUMMARY_FILE, MODEL_RESULTS_PATH)



# import os
# import json
# import shutil
# from collections import defaultdict

# def count_constraints(constraint_dict):
#     """
#     Count the total number of constraints in a constraint dictionary
#     """
#     total = 0
#     for key in constraint_dict:
#         # Skip the input_query and optimization fields
#         if key in ["input_query", "optimization"]:
#             continue
#         # Count all time ranges in the constraint categories
#         total += len(constraint_dict[key])
#     return total

# def process_json_file(file_path):
#     """
#     Process a single JSON file and return its constraint count
#     """
#     with open(file_path, 'r') as f:
#         data = json.load(f)
    
#     # The structure is always {filename: constraints}, so we get the first value
#     constraint_data = next(iter(data.values()))
#     return count_constraints(constraint_data)

# def categorize_files(file_constraints, num_groups=5):
#     """
#     Categorize files into difficulty groups based on constraint counts
#     Returns a dictionary of {group_name: [file_paths]}
#     """
#     # Sort files by constraint count (descending)
#     sorted_files = sorted(file_constraints.items(), key=lambda x: x[1], reverse=True)
#     total_files = len(sorted_files)
    
#     # Calculate how many files per group (approximately)
#     files_per_group = total_files // num_groups
    
#     categories = {
#         "80-100%": [],
#         "60-80%": [],
#         "40-60%": [],
#         "20-40%": [],
#         "0-20%": []
#     }
    
#     for i, (file_path, count) in enumerate(sorted_files):
#         if i < files_per_group:
#             categories["80-100%"].append((file_path, count))
#         elif i < 2 * files_per_group:
#             categories["60-80%"].append((file_path, count))
#         elif i < 3 * files_per_group:
#             categories["40-60%"].append((file_path, count))
#         elif i < 4 * files_per_group:
#             categories["20-40%"].append((file_path, count))
#         else:
#             categories["0-20%"].append((file_path, count))
    
#     return categories

# def create_output_folders(output_dir, categories):
#     """
#     Create output folders and copy files to their respective categories
#     """
#     # Create the main output directory if it doesn't exist
#     if not os.path.exists(output_dir):
#         os.makedirs(output_dir)
    
#     # Create category subdirectories
#     for category in categories:
#         category_dir = os.path.join(output_dir, category)
#         if not os.path.exists(category_dir):
#             os.makedirs(category_dir)
        
#         # Copy files to their category directory
#         for file_path, _ in categories[category]:
#             file_name = os.path.basename(file_path)
#             dest_path = os.path.join(category_dir, file_name)
#             shutil.copy2(file_path, dest_path)

# def generate_summary_file(summary_path, categories):
#     """
#     Generate a summary text file showing all constraints ranked by difficulty
#     """
#     with open(summary_path, 'w') as f:
#         f.write("Constraint Files Ranked by Difficulty\n")
#         f.write("====================================\n")
        
#         for category in ["80-100%", "60-80%", "40-60%", "20-40%", "0-20%"]:
#             f.write(f"\n=============== {category} Most Constrained ===============n\n")
            
#             # Sort files in this category by constraint count (descending)
#             sorted_files = sorted(categories[category], key=lambda x: x[1], reverse=True)
            
#             for file_path, count in sorted_files:
#                 file_name = os.path.basename(file_path)
#                 f.write(f"{file_name}: {count} constraints\n")

# def main(input_folder, output_folder, summary_file_path):
#     """
#     Main function to process all JSON files in the input folder
#     """
#     # Dictionary to store file paths and their constraint counts
#     file_constraints = {}
    
#     # Process all JSON files in the input folder
#     for file_name in os.listdir(input_folder):
#         if file_name.endswith('.json'):
#             file_path = os.path.join(input_folder, file_name)
#             try:
#                 constraint_count = process_json_file(file_path)
#                 file_constraints[file_path] = constraint_count
#             except (json.JSONDecodeError, KeyError) as e:
#                 print(f"Error processing {file_name}: {e}")
#                 continue
    
#     # Categorize files into difficulty groups
#     categories = categorize_files(file_constraints)
    
#     # Create output folders with categorized files
#     create_output_folders(output_folder, categories)
    
#     # Generate the summary text file
#     generate_summary_file(summary_file_path, categories)
    
#     print(f"Processing complete. Results saved to {output_folder}")
#     print(f"Summary file created at {summary_file_path}")

# if __name__ == "__main__":
#     # Configuration - change these paths as needed
#     INPUT_FOLDER = "constraint_satisfaction/calendar"  # Folder containing the JSON files
#     OUTPUT_FOLDER = "bucketed_constraints/bucketed_result_groups/calendar"  # Where to save the categorized files
#     SUMMARY_FILE = "bucketed_constraints/constraint_summary_calendar.txt"  # Path for the summary text file
    
#     # Run the program
#     main(INPUT_FOLDER, OUTPUT_FOLDER, SUMMARY_FILE)


