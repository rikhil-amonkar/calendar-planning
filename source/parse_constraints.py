import argparse
from openai import OpenAI
import json
with open("../../scheduling_key.json") as f:
    key = json.load(f)["openai"]
client = OpenAI(api_key=key)

# Argument parsing
parser = argparse.ArgumentParser(description="")
parser.add_argument('--task', choices=['calendar', 'trip', 'meeting', 'all'], required=True, help="")
args = parser.parse_args()

CALENDAR_PROMPT = """
Your job is to extract a JSON object from a task description. Here is an example.
Task: You need to schedule a meeting for Raymond, Billy and Donald for half an hour between the work hours of 9:00 to 17:00 on Monday. \n\nHere are the existing schedules for everyone during the day: \nRaymond has blocked their calendar on Monday during 9:00 to 9:30, 11:30 to 12:00; \nBilly has meetings on Monday during 10:00 to 10:30, 12:00 to 13:00; \nDonald has meetings on Monday during 9:00 to 9:30, 10:00 to 11:00; \n\nBilly would like to avoid more meetings on Monday after 15:00. Find a time that works for everyone's schedule and constraints.
Output:
{
    "meerting_duration:": 0.5,
    "disallowed_ranges": [
        {
            "day": "Monday",
            "start": 0,
            "end": 9
        },
        {
            "day": "Monday",
            "start": 17,
            "end": 24
        },
        {
            "day": "Monday",
            "start": 9,
            "end": 9.5
        },
        {
            "day": "Monday",
            "start": 11.5,
            "end": 12
        },
        {
            "day": "Monday",
            "start": 10,
            "end": 10.5
        },
        {
            "day": "Monday",
            "start": 12,
            "end": 13
        },
        {
            "day": "Monday",
            "start": 9,
            "end": 9.5
        },
        {
            "day": "Monday",
            "start": 10,
            "end": 11
        },
        {
            "day": "Monday",
            "start": 15,
            "end": 24
        }
    ]
}
"""

TRIP_PROMPT = """
Your job is to extract a JSON object from a task description. Here is an example.
Task: You plan to visit 3 European cities for 10 days in total. You only take direct flights to commute between cities. You would like to visit Venice for 6 days. You have to attend a workshop in Venice between day 5 and day 10. You want to spend 2 days in Mykonos. You plan to stay in Vienna for 4 days.\n\nHere are the cities that have direct flights:\nMykonos and Vienna, Vienna and Venice.\n\nFind a trip plan of visiting the cities for 10 days by taking direct flights to commute between them.
Output:
{
    "trip_length": 10,
    "city_length": [
        {
            "city": "Venice",
            "days": 6
        },
        {
            "city": "Mykonos",
            "days": 2
        },
        {
            "city": "Vienna",
            "days": 4
        }
    ],
    "city_day_ranges": [
        {
            "city": "Venice",
            "start": 5,
            "end": 10
        }
    ],
    "direct_flights": [
        {
            "from": "Mykonos",
            "to": "Vienna"
        },
        {
            "from": "Vienna",
            "to": "Venice"
        }
    ]
}
"""

def transform_meeting_constraints(entry: dict) -> dict:
    raw_constr = entry.get("constraints", [])
    dist_mat   = entry.get("dist_matrix", {})

    # 1) flatten dist_matrix → travel_distances
    travel_distances = [
        {
            "place": {"from": src, "to": dst},
            "walking_time": mins
        }
        for src, row in dist_mat.items()
        for dst, mins in row.items()
    ]

    # 2) pull out 'start' and 'people_to_meet' from raw_constr
    start = {
                "location": raw_constr[0][0],
                "time_of_day": raw_constr[0][1]
            }
    people_to_meet = []
    for c in raw_constr[1:]:
        people_to_meet.append({
                "name": c[0],
                "location": c[1],
                "time_of_day": {
                    "from": c[2].split(" to ")[0],
                    "to": c[2].split(" to ")[1]
                },
                "min_meeting_duration": c[3]
            })

    return {
        "travel_distances": travel_distances,
        "start": start,
        "people_to_meet": people_to_meet
    }

def extract_constraint(query, task):
    if task == "calendar":
        example = CALENDAR_PROMPT
    elif task == "trip":
        example = TRIP_PROMPT
    
    prompt = example + "Given the following task description:\n" + query + "\nExtract the constraints in the same JSON format as above."
    return evaluate_by_gpt(prompt)

def evaluate_by_gpt(text, type="json_object"):
    response = client.responses.create(
        model="gpt-4.1",
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
        max_output_tokens=10000,
        top_p=1,
        store=True
    )
    output_json = response.output[0].content[0].text
    #print(f"Output JSON: {output_json}")
    output_json = json.loads(output_json)
    return output_json

task_name_map = {
    "calendar": "calendar_scheduling",
    "trip": "trip_planning",
    "meeting": "meeting_planning"
}

if args.task == "all":
    tasks = ["calendar", "trip", "meeting"]
else:
    tasks = [args.task]

for task in tasks:
    # load the 100-example file
    infile = f"../data/{task_name_map[task]}_100.json"
    with open(infile, 'r', encoding='utf-8') as f:
        examples = json.load(f)

    # build constraints dict
    out_dict = {}
    counter = 0
    for ex_id, ex in examples.items():
        print(counter)
        counter += 1
        print(f"Processing {ex_id}...")
        query = ex.get("prompt_0shot", "")
        golden = ex.get("golden_plan", "")
        if task == "meeting": 
            cons = transform_meeting_constraints(ex)
        else:
        # call your extractor
            cons = extract_constraint(query, task)
        out_dict[ex_id] = {
            "prompt_0shot": query,
            "golden_plan": golden,
            "constraints": cons
        }

    # write aggregated constraints
    outfile = f"../data/{task_name_map[task]}_100_constraints.json"
    with open(outfile, 'w', encoding='utf-8') as f_out:
        json.dump(out_dict, f_out, ensure_ascii=False, indent=2)

    print(f"Saved constraints for {task} → {outfile}")