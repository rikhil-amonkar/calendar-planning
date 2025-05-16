import argparse
import os
import subprocess
from openai import OpenAI
import json
with open("../../scheduling_key.json") as f:
    key = json.load(f)["openai"]
client = OpenAI(api_key=key)

def extract_answer(answer_str, task):
    prompt = {
        "calendar": "Given the following time range:\n" + answer_str + "\nExtract the meeting start day and time in a JSON like {\"start_day\": \"Monday\", \"start_time\": \"14:30\"}. The time should be in 24-hour format. If no end time is given, assume the end time is one hour later than the start time. If no day given, assume the day is Monday.",
        "trip": "Given the following itinerary:\n" + answer_str + "\nExtract the days spent in each city in a JSON format like {\"itinerary\": [{\"city\": \"Paris\", \"days\": [1,2,3]}}, {\"city\": \"Rome\", \"days\": [3,4]}]}. If one flies from one city to another, the day of the flight should be included in both cities. If no itinerary is given, output an empty JSON.",
        "meeting": "Given the following meeting schedule:\n" + answer_str + "\nExtract the start time and the person of each meeting in a JSON format like {\"itinerary\": [{\"start_time\": \"14:30\", \"person\": \"Alice\"}, {\"start_time\": \"16:30\", \"person\": \"Bob\"}]}. The time should be in 24-hour format."
    }
    return evaluate_by_gpt(prompt[task])

def evaluate_by_gpt(text, type="json_object"):
    response = client.responses.create(
        model="gpt-4.1-nano",
        input=[
            {
            "role": "user",
            "content": [
                {
                    "type": "input_text",
                    "text": text
                }
            ]
            }
        ],
        text={
            "format": {
            "type": type
            }
        },
        reasoning={},
        tools=[],
        temperature=0,
        max_output_tokens=1000,
        top_p=1,
        store=True
    )
    output_json = response.output[0].content[0].text
    #print(f"Output JSON: {output_json}")
    output_json = json.loads(output_json)
    return output_json


def evaluate_output(pred, gold, task):
    if isinstance(gold, list):
        gold = "\n".join(gold)
    if not pred or "Error" in pred:
        pred_range = {}
    else:
        pred_range = extract_answer(pred, task)
    if not pred_range or "itinerary" in pred_range and len(pred_range["itinerary"]) == 0:
        return False
    gold_range = extract_answer(gold, task)
    print(f"Pred: {pred_range}\nGold: {gold_range}\n")
    return pred_range == gold_range

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
    elif '/' in model:
        model = model.split('/')[-1]
    for task in tasks:
        success_count = 0
        total_count = 0
        error_count = 0
        by_example = {}
        with open(f"../data/{task_name_map[task]}_100.json") as f:
            data = json.load(f)
        for idx, (id, example) in enumerate(data.items()):
            try:
                pred = open(f"../output/SMT/{model}/{task}/output/{id}.out").read()
            except FileNotFoundError:
                print(f"Prediction file not found for id {id}, skipping.")
                continue
            gold = example["golden_plan"]
            status = ""
            if not pred or "Error" in pred:
                error_count += 1
                status = "Error"
            elif evaluate_output(pred, gold, task):
                success_count += 1
                status = "Success"
            else:
                status = "Failure"
            total_count += 1
            print(total_count)
            by_example[id] = {
                "pred": pred,
                "gold": gold,
                "status": status
            }
        report_data = {
            "success_rate": f"{success_count / total_count * 100:.2f}%" if total_count > 0 else "N/A",
            "total_examples": total_count,
            "correct_examples": success_count,
            "error_examples": error_count,
            "examples": by_example
        }
        with open(f"../output/SMT/{model}/{task}/report.json", "w") as f:
            json.dump(report_data, f, indent=4)

