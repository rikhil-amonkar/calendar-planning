import argparse
import os
import subprocess
from openai import OpenAI
import json
with open("../../drums_llm_key.json") as f:
    key = json.load(f)["openai"]
client = OpenAI(api_key=key)

def evaluate_output(pred, gold):
    if isinstance(gold, list):
        gold = gold[0]
    response = client.responses.create(
        model="gpt-4.1-nano",
        input=[
            {
            "role": "user",
            "content": [
                {
                "type": "input_text",
                "text": "You are given two model outputs:\n1. " + pred + "\n2. " + gold + "\nAre the two identical even though they can be expressed differently? Answer in a JSON like {\"answer\": \"yes\"} or {\"answer\": \"no\"}."
                }
            ]
            }
        ],
        text={
            "format": {
            "type": "json_object"
            }
        },
        reasoning={},
        tools=[],
        temperature=0,
        max_output_tokens=20,
        top_p=1,
        store=True
    )
    return json.loads(response.output[0].content[0].text)["answer"]

# Argument parsing
parser = argparse.ArgumentParser(description="")
parser.add_argument('--task', choices=['calendar', 'trip', 'meeting', 'all'], required=True, help="")
parser.add_argument('--model', required=True, nargs='+', help="")
args = parser.parse_args()

task_name_map = {
    "calendar": "calendar_scheduling",
    "trip": "trip_planning",
    "meeting": "meeting_planning"
}

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
        success_count = 0
        total_count = 0
        print(total_count)
        with open(f"../natural-plan/data/{task_name_map[task]}.json") as f:
            data = json.load(f)
        for idx, (id, example) in enumerate(data.items()):
            try:
                pred = open(f"../output/SMT/{model}/{task}/output/{id}.out").read()
            except FileNotFoundError:
                print(f"Prediction file not found for id {id}, skipping.")
                continue
            gold = example["golden_plan"]
            if evaluate_output(pred, gold) == "yes":
                success_count += 1
            total_count += 1
        with open(f"../output/SMT/{model}/{task}/report.txt", "w") as f:
            f.write(f"Success rate: {success_count / total_count * 100:.2f}%\n")
            f.write(f"Total examples: {total_count}\n")
            f.write(f"Correct examples: {success_count}\n")
