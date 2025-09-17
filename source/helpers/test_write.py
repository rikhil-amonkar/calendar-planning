import os
import json

# Define the test directory
base_dir = "../output/SMT/Qwen2.5-Coder-32B-Instruct/meeting/n_pass/test_write_example/1_pass"
os.makedirs(base_dir, exist_ok=True)

# Test data to write
test_data = {"test": "success"}

# Write the test file
file_path = os.path.join(base_dir, "test.json")
with open(file_path, "w") as f:
    json.dump(test_data, f)

print("Test file written:", os.path.abspath(file_path)) 