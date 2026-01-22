import os
import json
import shutil
from collections import defaultdict

def count_constraints(constraint_dict):
    """
    Count the total number of constraints in the new meeting planning format:
    1. start location/time (counts as 1)
    2. Each person in people_to_meet (counts as 1 per person)
    3. Each person's min_duration (counts as 1 if present)
    4. Each travel_distance (counts as 1)
    """
    total = 0
    
    # Count start location/time as 1
    if "start" in constraint_dict:
        total += 1
    
    # Count people_to_meet constraints
    if "people_to_meet" in constraint_dict:
        for person in constraint_dict["people_to_meet"]:
            total += 1  # Count the person constraint itself
            if "min_duration" in person:
                total += 1  # Count the min_duration constraint
    
    # Count travel_distances
    if "travel_distances" in constraint_dict:
        total += len(constraint_dict["travel_distances"])
    
    return total

def process_json_file(file_path):
    """
    Process the new format JSON file and return a dictionary of example_id -> constraint_count
    """
    with open(file_path, 'r') as f:
        data = json.load(f)
    
    # The structure is {example_id: {constraints: {...}}}
    example_constraints = {}
    for example_id, example_data in data.items():
        if "constraints" in example_data:
            constraint_count = count_constraints(example_data["constraints"])
            example_constraints[example_id] = {
                "constraint_count": constraint_count,
                "data": example_data
            }
    
    return example_constraints

def categorize_examples(example_constraints, num_groups=5):
    """
    Categorize examples into difficulty groups based on constraint counts
    Returns a dictionary of {group_name: [(example_id, constraint_count, data)]}
    """
    # Sort examples by constraint count (descending)
    sorted_examples = sorted(
        example_constraints.items(), 
        key=lambda x: x[1]["constraint_count"], 
        reverse=True
    )
    total_examples = len(sorted_examples)
    
    # Calculate how many examples per group (approximately)
    examples_per_group = total_examples // num_groups
    
    categories = {
        "80-100%": [],
        "60-80%": [],
        "40-60%": [],
        "20-40%": [],
        "0-20%": []
    }
    
    for i, (example_id, info) in enumerate(sorted_examples):
        constraint_count = info["constraint_count"]
        data = info["data"]
        
        if i < examples_per_group:
            categories["80-100%"].append((example_id, constraint_count, data))
        elif i < 2 * examples_per_group:
            categories["60-80%"].append((example_id, constraint_count, data))
        elif i < 3 * examples_per_group:
            categories["40-60%"].append((example_id, constraint_count, data))
        elif i < 4 * examples_per_group:
            categories["20-40%"].append((example_id, constraint_count, data))
        else:
            categories["0-20%"].append((example_id, constraint_count, data))
    
    return categories

def create_output_folders(output_dir, categories):
    """
    Create output folders and save JSON files to their respective categories
    """
    # Create the main output directory if it doesn't exist
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)
    
    # Create category subdirectories and save files
    for category in categories:
        category_dir = os.path.join(output_dir, category)
        if not os.path.exists(category_dir):
            os.makedirs(category_dir)
        
        # Save each example as a JSON file in its category directory
        for example_id, constraint_count, data in categories[category]:
            # Create a JSON file with the example data
            output_data = {example_id: data}
            file_name = f"{example_id}.json"
            dest_path = os.path.join(category_dir, file_name)
            
            with open(dest_path, 'w') as f:
                json.dump(output_data, f, indent=2)

def generate_summary_file(summary_path, categories):
    """
    Generate a summary text file showing all examples ranked by difficulty
    """
    with open(summary_path, 'w') as f:
        f.write("Meeting Planning Examples Ranked by Constraint Count\n")
        f.write("=" * 60 + "\n")
        f.write("\n")
        
        for category in ["80-100%", "60-80%", "40-60%", "20-40%", "0-20%"]:
            f.write(f"\n{'=' * 20} {category} Most Constrained {'=' * 20}\n")
            f.write(f"Total examples in this bucket: {len(categories[category])}\n")
            f.write("-" * 60 + "\n")
            
            # Sort files in this category by constraint count (descending)
            sorted_examples = sorted(
                categories[category], 
                key=lambda x: x[1], 
                reverse=True
            )
            
            for example_id, constraint_count, _ in sorted_examples:
                f.write(f"{example_id}: {constraint_count} constraints\n")

def main(input_file, output_folder, summary_file_path):
    """
    Main function to process the meeting planning JSON file
    """
    print(f"Processing {input_file}...")
    
    # Process the JSON file
    example_constraints = process_json_file(input_file)
    print(f"Found {len(example_constraints)} examples")
    
    # Categorize examples into difficulty groups
    categories = categorize_examples(example_constraints)
    
    # Create output folders with categorized files
    create_output_folders(output_folder, categories)
    
    # Generate the summary text file
    generate_summary_file(summary_file_path, categories)
    
    print(f"\nProcessing complete!")
    print(f"Results saved to {output_folder}")
    print(f"Summary file created at {summary_file_path}")
    
    # Print summary statistics
    print("\nBucket distribution:")
    for category in ["80-100%", "60-80%", "40-60%", "20-40%", "0-20%"]:
        count = len(categories[category])
        if categories[category]:
            min_constraints = min(x[1] for x in categories[category])
            max_constraints = max(x[1] for x in categories[category])
            print(f"  {category}: {count} examples (constraints: {min_constraints}-{max_constraints})")
        else:
            print(f"  {category}: {count} examples")

if __name__ == "__main__":
    # Configuration
    INPUT_FILE = "improved/meeting_planning_100_constraints.json"  # Input JSON file
    OUTPUT_FOLDER = "output/Buckets/NEW_BUCKETS"  # Where to save the categorized files
    SUMMARY_FILE = "output/Buckets/NEW_BUCKETS/constraint_summary_meeting.txt"  # Path for the summary text file
    
    # Get absolute paths
    base_dir = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    input_path = os.path.join(base_dir, INPUT_FILE)
    output_path = os.path.join(base_dir, OUTPUT_FOLDER)
    summary_path = os.path.join(base_dir, SUMMARY_FILE)
    
    # Run the program
    main(input_path, output_path, summary_path)
