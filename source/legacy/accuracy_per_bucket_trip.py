import json
import re

def parse_constraint_file(file_path):
    constraint_groups = {}
    current_group = None
    
    with open(file_path, 'r') as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
                
            # Check for group headers
            if line.startswith("===============") and "Most Constrained" in line:
                current_group = line.strip("= ").split()[0]
                constraint_groups[current_group] = []
                continue
                
            # Parse example lines
            if current_group and line.endswith("constraints"):
                # Extract the example ID (remove "_output.json" and anything after)
                example_id = line.split(":")[0].replace("_output.json", "")
                constraint_groups[current_group].append(example_id)
                
    return constraint_groups

def compare_itineraries(final, expected):
    """Compare two itineraries for exact match of day ranges and places"""
    if len(final) != len(expected):
        return False
    
    for f_item, e_item in zip(final, expected):
        if f_item["day_range"] != e_item["day_range"] or f_item["place"] != e_item["place"]:
            return False
    return True

def check_example_accuracy(json_file_path, constraint_groups):
    group_results = {group: {"correct": 0, "total": 0} for group in constraint_groups}
    example_status = {}
    
    with open(json_file_path, 'r') as f:
        data = json.load(f)
        
        # Check each example in the 0shot section
        for example in data.get("0shot", []):
            example_id = example["count"]
            final_itinerary = example["final_program_time"]["itinerary"]
            expected_itinerary = example["expected_time"]["itinerary"]
            
            # Check if all itinerary components match
            is_correct = compare_itineraries(final_itinerary, expected_itinerary)
            
            example_status[example_id] = is_correct
            
            # Update group statistics
            for group, examples in constraint_groups.items():
                if example_id in examples:
                    group_results[group]["total"] += 1
                    if is_correct:
                        group_results[group]["correct"] += 1
                    break
                    
    return group_results, example_status

def generate_output_file(input_file_path, output_file_path, constraint_groups, example_status, group_results):
    with open(input_file_path, 'r') as infile, open(output_file_path, 'w') as outfile:
        current_group = None
        
        for line in infile:
            line = line.strip()
            if not line:
                outfile.write("\n")
                continue
                
            # Write group headers as-is
            if line.startswith("===============") and "Most Constrained" in line:
                current_group = line.strip("= ").split()[0]
                outfile.write(line + "\n")
                continue
                
            # Write other headers as-is
            if line.startswith("Trip Planning") or line.startswith("(Constraint count"):
                outfile.write(line + "\n")
                continue
                
            # Process example lines
            if line.endswith("constraints"):
                example_full = line.split(":")[0]
                example_id = example_full.replace("_output.json", "")
                constraints = line.split(":")[1].strip()
                
                status = "UNKNOWN"
                if example_id in example_status:
                    status = "CORRECT" if example_status[example_id] else "INCORRECT"
                
                outfile.write(f"{example_full}: {constraints} - {status}\n")
            else:
                outfile.write(line + "\n")
                
        # Write accuracy statistics at the end
        outfile.write("\n\nAccuracy Statistics:\n")
        outfile.write("==================================================\n")
        for group in constraint_groups:
            correct = group_results[group]["correct"]
            total = group_results[group]["total"]
            accuracy = (correct / total) * 100 if total > 0 else 0
            outfile.write(f"{group}% Most Constrained: {correct}/{total} correct ({accuracy:.2f}%)\n")

def main():
    # File paths - change these as needed
    constraint_file_path = "bucketed_constraints/constraint_summary_trip.txt"
    json_file_path = "trip_planning/100_random_0shot_code_outputs/DS-R1-FULL_code_trip_results.json"
    output_file_path = "bucketed_constraints/constraint_summary_trip_code_accuracy.txt"
    
    # Step 1: Parse the constraint file to group examples by difficulty
    constraint_groups = parse_constraint_file(constraint_file_path)
    
    # Step 2: Check accuracy of each example in the JSON file
    group_results, example_status = check_example_accuracy(json_file_path, constraint_groups)
    
    # Step 3: Generate the output file with CORRECT/INCORRECT markings and accuracy stats
    generate_output_file(constraint_file_path, output_file_path, constraint_groups, example_status, group_results)
    
    print(f"Processing complete. Results written to {output_file_path}")

if __name__ == "__main__":
    main()

