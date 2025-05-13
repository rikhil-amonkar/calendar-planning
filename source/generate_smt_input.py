import argparse
# from openai import OpenAI
import json
import os
from kani import Kani
from kani.engines.huggingface import HuggingEngine
from kani.engines.openai import OpenAIEngine
import asyncio
import re
import time

# Argument parsing
parser = argparse.ArgumentParser(description="")
parser.add_argument('--task', choices=['calendar', 'trip', 'meeting', 'all'], required=True, help="")
parser.add_argument('--model', required=True, nargs='+', help="")
parser.add_argument('--start', type=int, default=0, help="Starting index for the examples")
parser.add_argument('--end', type=int, default=-1, help="Ending index for the examples")
args = parser.parse_args()

with open("../../scheduling_key.json") as f:
    keys = json.load(f)

def initialize_model(model_name, keys):
    """Initializes the Kani AI model based on the model name."""
    print(f"Running model: {model_name}")
    if model_name.startswith("gpt") or model_name.startswith("o"):
        if model_name == "o3-mini":
            model_name = "o3-mini-2025-01-31"
        elif model_name == "gpt-4o-mini":
            model_name = "gpt-4o-mini-2024-07-18"
        engine = OpenAIEngine(keys["openai"], model=model_name, max_context_size=20000)
    elif model_name == "DeepSeek-R1":
        engine = OpenAIEngine(keys["deepseek"], model="deepseek-reasoner", api_base="https://api.deepseek.com", max_context_size=20000)
    elif model_name == "DeepSeek-V3":
        engine = OpenAIEngine(keys["deepseek"], model="deepseek-chat", api_base="https://api.deepseek.com", max_context_size=20000)
    else:
        engine = HuggingEngine(model_id=model_name)

    ai = Kani(engine, system_prompt="")
    return ai

for model_name in args.model:
    ai = initialize_model(model_name, keys)

    task_name_map = {
        "calendar": "calendar_scheduling",
        "trip": "trip_planning",
        "meeting": "meeting_planning"
    }

    async def run_model(prompt):
        response = await ai.chat_round_str(prompt)
        return response

    if args.task == "all":
        tasks = ["calendar", "trip", "meeting"]
    else:
        tasks = [args.task]

    def extract_code(response_txt):
        matches = re.findall(r"```python\s*(.*?)```", response_txt, re.DOTALL)
        return matches[-1].strip() if matches else ""

    for task in tasks:
        print(f"Running task: {task}")
        with open(f"../data/{task_name_map[task]}_100.json") as f:
            data = json.load(f)

        for idx, (id, example) in enumerate(data.items()):
            if idx < args.start or (args.end != -1 and idx >= args.end):
                continue
            print(f"Running example: {id}")
            prompt = "Given the following scheduling problem:\n"
            prompt += f"{example['prompt_0shot']}\n"
            prompt += "Write a Python program that solves it using the Z3 solver. Alway surround your final code with ```python\nYOUR_CODE\n```.\n"
            while True:
                try:
                    response_txt = asyncio.run(run_model(prompt))
                    generated_code = extract_code(response_txt)
                    break # Exit the loop if successful
                except Exception as e:
                    print(f"An error occurred: {e}. Retrying in 5 seconds...")
                    time.sleep(5)
                    ai = initialize_model(model_name, keys)

            #print(response_txt)

            model_short_name = model_name.split("/")[-1] if "/" in model_name else model_name
            output_dir = f"../output/SMT/{model_short_name}/{task}/code"
            output_fname = f"{id}.py"
            os.makedirs(output_dir, exist_ok=True)
            # Save raw response text
            output_path = os.path.join(output_dir, output_fname)
            with open(output_path, "w") as f:
                f.write(generated_code)