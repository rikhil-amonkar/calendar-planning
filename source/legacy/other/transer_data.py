# Specify the source and destination file paths
source_file = 'meeting_planning.json'
destination_file = 'meeting_all_1000_prompts.json'

import json

# Open the source file in read mode and the destination file in write mode
with open(source_file, 'r') as source:
    data = json.load(source)  # Load the JSON data from the source file

with open(destination_file, 'w') as destination:
    json.dump(data, destination, indent=4)  # Write the JSON data to the destination file

print("Data has been copied as JSON from source_file.json to destination_file.json")
