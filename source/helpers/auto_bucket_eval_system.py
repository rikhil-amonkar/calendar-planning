import os
import json
import argparse
from pathlib import Path

def main():
    # Set up argument parsing
    parser = argparse.ArgumentParser(description='Classify bucket results based on evaluation.json files')
    parser.add_argument('--input_path', type=str, required=True, help='Path to the folder containing example folders')
    parser.add_argument('--output_file', type=str, required=True, help='Path to the output text file')
    parser.add_argument('--method', type=str, required=True, 
                        choices=['Plan', 'Python', 'Python Revision', 'SMT', 'SMT Revision'],
                        help='Method to evaluate (determines if we look at all passes or just first)')
    
    args = parser.parse_args()
    
    # Determine if we need to look at all passes or just the first
    use_all_passes = "Revision" in args.method
    
    # Read the output file to get the list of examples and their constraint counts
    example_constraints = {}
    bucket_ranges = []
    current_bucket = None
    
    try:
        with open(args.output_file, 'r') as f:
            lines = f.readlines()
            
            for line in lines:
                line = line.strip()
                # Check for bucket headers
                if line.startswith("===============") and "%" in line and "Most Constrained" in line:
                    # Extract the percentage range
                    percent_range = line.split(" ")[1]
                    bucket_ranges.append(percent_range)
                    current_bucket = percent_range
                elif line and not line.startswith("=") and not line.startswith("Constraint") and not line.startswith("Model:") and "correct" not in line:
                    # This is an example line
                    if "constraints" in line and ":" in line:
                        parts = line.split(":")
                        example_name = parts[0].strip()
                        constraints_part = parts[1].strip()
                        constraint_count = int(constraints_part.split(" ")[0])
                        
                        example_constraints[example_name] = {
                            "constraint_count": constraint_count,
                            "bucket": current_bucket,
                            "line": line
                        }

                    # Else for zebra
                    elif line and not line.startswith("=") and not line.startswith("Constraint") and not line.startswith("Model:") and "correct" not in line:
                        # This is an example line
                        if ":" in line:
                            parts = line.split(":")
                            example_name = parts[0].strip()

                            # Case 1: classic "constraints"
                            if "constraints" in line:
                                constraints_part = parts[1].strip()
                                constraint_count = int(constraints_part.split(" ")[0])

                            # Case 2: ZebraLogic "NxM = number"
                            elif "=" in parts[1]:
                                constraints_part = parts[1].strip()
                                constraint_count = int(constraints_part.split("=")[-1].split()[0])

                            else:
                                continue

                            example_constraints[example_name] = {
                                "constraint_count": constraint_count,
                                "bucket": current_bucket,
                                "line": line
                            }

    except FileNotFoundError:
        print(f"Output file {args.output_file} not found. Please check the path.")
        return
    
    # Now process each example folder
    input_path = Path(args.input_path)
    if not input_path.exists():
        print(f"Input path {args.input_path} does not exist.")
        return
    
    # Get all example folders
    example_folders = [f for f in input_path.iterdir() if f.is_dir()]
    
    # For each example, check if it's correct
    for example_name in example_constraints.keys():
        # Find the matching folder
        folder_name = example_name.replace("_output.json", "")
        matching_folder = None
        
        for folder in example_folders:
            if folder.name.startswith(folder_name):
                matching_folder = folder
                break

        print(f"Processing {example_name}, looking for folder {folder_name}")
        if matching_folder:
            print(f"Found folder: {matching_folder}")
        else:
            print(f"NO MATCH for {example_name}")

        
        if not matching_folder:
            print(f"Warning: No folder found for example {example_name}")
            example_constraints[example_name]["correct"] = False
            continue
        
        # Check if we need to look at all passes or just the first
        if use_all_passes:
            correct = False
            for pass_num in range(1, 6):
                pass_folder = matching_folder / f"{pass_num}_pass"
                eval_file = pass_folder / "evaluation.json"
                if eval_file.exists():
                    try:
                        with open(eval_file, 'r') as f:
                            data = json.load(f)
                            if data.get("constraints_satisfied", False):
                                correct = True
                                break
                    except (json.JSONDecodeError, IOError):
                        pass

            # FALLBACK: single_pass layout -> evaluation.json directly in example folder
            if not correct:
                direct_eval = matching_folder / "evaluation.json"
                if direct_eval.exists():
                    try:
                        with open(direct_eval, 'r') as f:
                            data = json.load(f)
                            correct = data.get("constraints_satisfied", False)
                    except (json.JSONDecodeError, IOError):
                        pass

            example_constraints[example_name]["correct"] = correct

        else:
            pass_folder = matching_folder / "1_pass"
            eval_file = pass_folder / "evaluation.json"

            # FALLBACK: single_pass layout -> evaluation.json directly in example folder
            if not eval_file.exists():
                eval_file = matching_folder / "evaluation.json"

            if eval_file.exists():
                try:
                    with open(eval_file, 'r') as f:
                        data = json.load(f)
                        example_constraints[example_name]["correct"] = data.get("constraints_satisfied", False)
                except (json.JSONDecodeError, IOError):
                    example_constraints[example_name]["correct"] = False
            else:
                example_constraints[example_name]["correct"] = False
    
    # Now update the output file
    bucket_counts = {bucket: {"correct": 0, "total": 0} for bucket in bucket_ranges}
    
    try:
        with open(args.output_file, 'r') as f:
            content = f.read()
        
        # Replace each line with the correct/incorrect status
        for example_name, data in example_constraints.items():
            old_line = data["line"]
            new_line = old_line + " CORRECT" if data["correct"] else old_line + " INCORRECT"
            content = content.replace(old_line, new_line)
            
            # Update bucket counts
            if data["bucket"] in bucket_counts:
                bucket_counts[data["bucket"]]["total"] += 1
                if data["correct"]:
                    bucket_counts[data["bucket"]]["correct"] += 1
        
        # Update accuracy statistics
        accuracy_section = "\n\nAccuracy Statistics:\n========================================================"
        for bucket in bucket_ranges:
            if bucket_counts[bucket]["total"] > 0:
                accuracy = (bucket_counts[bucket]["correct"] / bucket_counts[bucket]["total"]) * 100
                accuracy_section += f"\n{bucket}% Most Constrained: {bucket_counts[bucket]['correct']}/{bucket_counts[bucket]['total']} correct ({accuracy:.1f}%)"
            else:
                accuracy_section += f"\n{bucket}% Most Constrained: 0/0 correct (0%)"
        
        # Replace the accuracy section
        if "Accuracy Statistics:" in content:
            old_accuracy_section = content.split("Accuracy Statistics:")[1]
            content = content.replace(old_accuracy_section, accuracy_section.split("Accuracy Statistics:")[1])
        else:
            content += accuracy_section
        
        # Write the updated content back to the file
        with open(args.output_file, 'w') as f:
            f.write(content)
            
        print(f"Successfully updated {args.output_file}")
        
    except IOError:
        print(f"Error writing to output file {args.output_file}")

if __name__ == "__main__":
    main()