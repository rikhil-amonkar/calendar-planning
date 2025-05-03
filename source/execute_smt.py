import argparse
import os
import subprocess

# Argument parsing
parser = argparse.ArgumentParser(description="")
parser.add_argument('--task', choices=['calendar', 'trip', 'meeting', 'all'], required=True, help="")
parser.add_argument('--model', required=True, nargs='+', help="")
args = parser.parse_args()

if args.task == "all":
    tasks = ["calendar", "trip", "meeting"]
else:
    tasks = [args.task]

for model in args.model:
    if model == "o3-mini":
        model = "o3-mini-2025-01-31"
    elif model == "gpt-4o-mini":
        model = "gpt-4o-mini-2024-07-18"
    for task in tasks:
        input_folder = f"../output/SMT/{model}/{task}/code"
        output_folder = f"../output/SMT/{model}/{task}/output/"
        os.makedirs(output_folder, exist_ok=True)

        for filename in os.listdir(input_folder):
            if filename.endswith(".py"):
                script_path = os.path.join(input_folder, filename)
                output_path = os.path.join(output_folder, filename.replace(".py", ".out"))
                with open(output_path, "w") as outfile:
                    result = subprocess.run(
                        ["python3", script_path],
                        stdout=outfile,
                        stderr=subprocess.STDOUT
                    )
                print(f"Ran {filename}, output saved to {output_path}")