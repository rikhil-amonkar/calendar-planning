import os
import json
import shutil
from collections import defaultdict

def count_constraints(constraint_dict):
    """
    Count the total number of constraints in a trip planning constraint dictionary
    Counts constraints from: trip_length (counts as 1), city_length, city_day_ranges, and direct_flights
    """
    total = 0
    
    # trip_length always counts as 1 constraint
    if "trip_length" in constraint_dict:
        total += 1
    
    # Count city_length constraints
    if "city_length" in constraint_dict:
        total += len(constraint_dict["city_length"])
    
    # Count city_day_ranges constraints
    if "city_day_ranges" in constraint_dict:
        total += len(constraint_dict["city_day_ranges"])
    
    # Count direct_flights constraints
    if "direct_flights" in constraint_dict:
        total += len(constraint_dict["direct_flights"])
    
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

def generate_summary_file(summary_path, categories):
    """
    Generate a summary text file showing all constraints ranked by difficulty
    """
    with open(summary_path, 'w') as f:
        f.write("Trip Planning Constraint Files Ranked by Difficulty\n")
        f.write("==================================================\n")
        f.write("(Constraint count includes: trip_length (1), city_length, city_day_ranges, direct_flights)\n\n")
        
        for category in ["80-100%", "60-80%", "40-60%", "20-40%", "0-20%"]:
            f.write(f"\n=============== {category} Most Constrained ===============\n")
            
            # Sort files in this category by constraint count (descending)
            sorted_files = sorted(categories[category], key=lambda x: x[1], reverse=True)
            
            for file_path, count in sorted_files:
                file_name = os.path.basename(file_path)
                f.write(f"{file_name}: {count} constraints\n")

def main(input_folder, output_folder, summary_file_path):
    """
    Main function to process all JSON files in the input folder
    """
    # Dictionary to store file paths and their constraint counts
    file_constraints = {}
    
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
    
    # Generate the summary text file
    generate_summary_file(summary_file_path, categories)
    
    print(f"Processing complete. Results saved to {output_folder}")
    print(f"Summary file created at {summary_file_path}")

if __name__ == "__main__":
    # Configuration - change these paths as needed
    INPUT_FOLDER = "constraint_satisfaction/trip"  # Folder containing the JSON files
    OUTPUT_FOLDER = "bucketed_constraints/bucketed_result_groups/trip"  # Where to save the categorized files
    SUMMARY_FILE = "bucketed_constraints/constraint_summary_trip.txt"  # Path for the summary text file
    
    # Run the program
    main(INPUT_FOLDER, OUTPUT_FOLDER, SUMMARY_FILE)

