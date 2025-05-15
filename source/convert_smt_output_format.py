import argparse
import os
import subprocess
from openai import OpenAI
import json
with open("../../scheduling_key.json") as f:
    key = json.load(f)["openai"]
client = OpenAI(api_key=key)

# Argument parsing
parser = argparse.ArgumentParser(description="")
parser.add_argument('--task', choices=['calendar', 'trip', 'meeting', 'all'], required=True, help="")
parser.add_argument('--model', required=True, nargs='+', help="")
parser.add_argument('--start', type=int, required=False, help="Starting index for processing examples")
args = parser.parse_args()

def extract_answer(answer_str, task):
    prompt = {
        "calendar": "Given the following time range:\n" + answer_str + "\nExtract the meeting start day and time in a JSON like {\"day\": \"Monday\", \"start_time\": \"14:30\", \"end_time\": \"15:30\"}. The time should be in 24-hour format. If no end time is given, assume the end time is one hour later than the start time. If no day given, assume the day is Monday. If no time range is given at all, output an empty JSON.",
        "trip": "Given the following itinerary:\n" + answer_str + "\nExtract the days spent in each city in a JSON format like {\"itinerary\": [{\"day_range\": \"Day 1-2\", \"place\": \"Reykjavik\"}, {\"day_range\": \"Day 2-4\", \"place\": \"Stockholm\"}......]}. Only keep the days in a city. If flying from city A to city B, that day should be included in both ranges for both cites. The day range should be inclusive. For example, arrving at a city in Day 2 and leaving on Day 8 will result in a day range of Day 2-8. If no itinerary is given, output an empty JSON.",
        "meeting": "Given the following meeting schedule:\n" + answer_str + "\nExtract the time and the person of each meeting in a JSON format like {\"itinerary\": [{\"action\": \"meet\", \"person\": \"David\",\"start_time\": \"13:00\", \"end_time\": \"14:00\"}, ...]}. Do not include location. Only keep the meeting times, and ignore time for starting, waiting, or traveling. The time should be converted to a 24-hour format."
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
        max_output_tokens=2000,
        top_p=1,
        store=True
    )
    output_json = response.output[0].content[0].text
    print(f"Output JSON: {output_json}")
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
        with open(f"../data/{task_name_map[task]}_100.json") as f:
            data = json.load(f)
        for idx, (id, example) in enumerate(data.items()):
            if args.start is not None and idx < args.start:
                continue
            print(idx)
            try:
                pred = open(f"../output/SMT/{model}/{task}/output/{id}.out").read()
            except FileNotFoundError:
                print(f"Prediction file not found for id {id}, skipping.")
                continue
            gold = example["golden_plan"]
            has_error = False
            if not pred or "Error" in pred:
                has_error = True
                pred_formatted = {}
            else:
                pred_formatted = extract_answer(pred, task)
            if isinstance(gold, list):
                gold = "\n".join(gold)
            gold_formatted = extract_answer(gold, task)
            print(f"Pred: {pred_formatted}\nGold: {gold_formatted}\n")
            output_dict = {
                "0shot": [
                    {
                        "count": id,
                        "final_program_time": pred_formatted,
                        "expected_time": gold_formatted,
                        "has_error": has_error,
                        "is_correct": gold_formatted == pred_formatted
                    }
                ]
            }
            output_dir = f"../output/SMT/{model}/{task}/formatted_output"
            os.makedirs(output_dir, exist_ok=True)
            with open(f"{output_dir}/{id}.json", "w") as f:
                json.dump(output_dict, f, indent=4)
