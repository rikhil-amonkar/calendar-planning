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
args = parser.parse_args()

with open(f"../data/bucketed_constraints_all_tasks.json") as f:
    bucketed_constraints = json.load(f)

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
        buckets = bucketed_constraints[task]
        with open(f"../output/SMT/{model}/{task}/report.json") as f:
            report = json.load(f)
            # count successes per bucket
            examples = report.get("examples", {})
            bucket_success = {}
            for bucket_name, bucket_info in buckets.items():
                cnt = 0
                for item in bucket_info["content"]:
                    eid = item["id"]
                    if examples.get(eid, {}).get("status") == "Success":
                        cnt += 1
                bucket_success[bucket_name] = cnt

            # print results
            print(f"Model={model}, Task={task_name_map[task]}")
            for bucket_name, success_cnt in bucket_success.items():
                desc = buckets[bucket_name]["description"]
                total = len(buckets[bucket_name]["content"])
                print(f"  {bucket_name} ({desc}): {success_cnt}/{total} successes")
        