import os
import json

# Path to the code directory
code_dir = '../output/SMT/DeepSeek-R1/calendar/code'
# Path to the JSON file (relative to code_dir)
json_path = '../data/calendar_scheduling_100.json'

# Get all .py files and their base names
py_files = [f for f in os.listdir(code_dir) if f.endswith('.py')]
py_basenames = set(os.path.splitext(f)[0] for f in py_files)

# Load JSON data
with open(json_path, 'r') as f:
    data = json.load(f)

# If the JSON is a dict, try to get a list from a key (adjust as needed)
if isinstance(data, dict):
    # Try to guess the key
    for key in ['names', 'files', 'list', 'items']:
        if key in data:
            data_list = data[key]
            break
    else:
        raise ValueError("Could not find a list of names in the JSON file.")
elif isinstance(data, list):
    data_list = data
else:
    raise ValueError("JSON file format not recognized.")

json_names = set(str(x) for x in data_list)

# Find .py basenames not in JSON
missing = py_basenames - json_names

print("Python files not included in JSON:")
for name in sorted(missing):
    print(name)