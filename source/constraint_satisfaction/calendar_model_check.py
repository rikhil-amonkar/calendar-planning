import os
import json

# Define the folder where the constraint dictionaries are located
calendar_folder = 'constraint_satisfaction/calendar'
report_filename = 'constraint_satisfaction/calendar_constraint_report.txt'  # Output file name

# Function to read and write each constraint dict with the number of constraints
def write_constraints_to_file():
    # List and sort all the JSON files in the calendar folder (sorting in case we want them in order)
    json_files = sorted([f for f in os.listdir(calendar_folder) if f.endswith('.json')])

    # Open the output report file for writing
    with open(report_filename, 'w') as report_file:
        # Iterate through the sorted files
        for filename in json_files:
            json_file_path = os.path.join(calendar_folder, filename)

            # Read the JSON content from the constraint dict file
            with open(json_file_path, 'r') as f:
                constraint_data = json.load(f)

            # Iterate through each scheduling example inside the JSON file
            for example_key, example_data in constraint_data.items():
                allowed_ranges = example_data.get('allowed_ranges', [])
                disallowed_ranges = example_data.get('disallowed_ranges', [])
                preferred_ranges = example_data.get('preferred_ranges', [])
                unpreferred_ranges = example_data.get('unpreferred_ranges', [])
                optimization = example_data.get('optimization', None)  # Get optimization (could be None)

                # Count optimization as 1 if it's not None or "nay", otherwise 0
                optimization_count = 1 if optimization not in [None, "any"] else 0

                # Calculate the total number of constraints for each type (including 0 if empty)
                total_constraints = (
                    len(allowed_ranges) +
                    len(disallowed_ranges) +
                    len(preferred_ranges) +
                    len(unpreferred_ranges) +
                    optimization_count  # Add optimization count based on the condition
                )

                # Write the constraint dictionary and the number of constraints to the file
                report_file.write(f"Example: {example_key}\n")
                report_file.write(f"Allowed Ranges: {allowed_ranges} (Count: {len(allowed_ranges)})\n")
                report_file.write(f"Disallowed Ranges: {disallowed_ranges} (Count: {len(disallowed_ranges)})\n")
                report_file.write(f"Preferred Ranges: {preferred_ranges} (Count: {len(preferred_ranges)})\n")
                report_file.write(f"Unpreferred Ranges: {unpreferred_ranges} (Count: {len(unpreferred_ranges)})\n")
                report_file.write(f"Optimization: {optimization} (Count: {optimization_count})\n")
                report_file.write(f"Total Constraints: {total_constraints}\n")
                report_file.write("-" * 40 + "\n")

    print(f"Report written to: {report_filename}")

# Run the program
write_constraints_to_file()
