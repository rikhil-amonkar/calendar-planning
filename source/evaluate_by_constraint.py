import argparse
from openai import OpenAI
import json
import os

with open("../../scheduling_key.json") as f:
    key = json.load(f)["openai"]
client = OpenAI(api_key=key)

# Argument parsing
parser = argparse.ArgumentParser(description="")
parser.add_argument('--task', choices=['calendar', 'trip', 'meeting', 'all'], required=True, help="")
parser.add_argument('--model', required=True, help="")
parser.add_argument('--output', choices=['plan', 'python', 'z3'], required=True, help="")
args = parser.parse_args()

def evaluate_calendar(constraints, pred_dict):
    pred_day = pred_dict["day"]
    pred_start = pred_dict["start_time"]
    pred_end = pred_dict["end_time"]
    # Convert time strings to numerical values
    if isinstance(pred_start, str):
        pred_start_parts = pred_start.split(":")
        try:
            pred_start = float(pred_start_parts[0]) + float(pred_start_parts[1]) / 60
        except ValueError:
            return False, {"unparsable": True}
    if isinstance(pred_end, str):
        pred_end_parts = pred_end.split(":")
        pred_end = float(pred_end_parts[0]) + float(pred_end_parts[1]) / 60
    meeting_duration = constraints["meeting_duration"]
    if (pred_end - pred_start) != meeting_duration:
        #print(pred_dict)
        print(f"Constraint violated: Meeting duration {pred_end - pred_start} does not match required {meeting_duration}")
        return False, {"meeting_duration": meeting_duration}
    for disallowed_range in constraints["disallowed_ranges"]:
        if disallowed_range["day"] == pred_day:
            if (pred_start >= disallowed_range["start"] and pred_start < disallowed_range["end"]) or \
               (pred_end > disallowed_range["start"] and pred_end <= disallowed_range["end"]) or \
               (pred_start <= disallowed_range["start"] and pred_end >= disallowed_range["end"]):
                #print(pred_dict)
                print(f"Constraint violated: {pred_day} {pred_start} - {pred_end} overlaps with {disallowed_range['start']} - {disallowed_range['end']}")
                #raise SystemExit
                return False, disallowed_range
    return True, {}

def evaluate_trip(constraints, pred_dict):
    # parse the predicted itinerary segments
    segments = []
    for seg in pred_dict["itinerary"]:
        # "Day X-Y"
        dr = seg["day_range"].replace("Day ", "")
        if "-" in dr:
            start_s, end_s = dr.split("-")
        else:
            start_s, end_s = [dr, dr]
        start, end = int(start_s), int(end_s)
        segments.append({"place": seg["place"], "start": start, "end": end})

    # 1) check full coverage from day 1 to total_days, with no gaps/overlaps
    total = constraints.get("trip_length")
    if not segments or segments[0]["start"] != 1 or segments[-1]["end"] != total:
        print(f"Constraint violated: itinerary must cover days 1–{total}")
        return False, {"total_days": total}
    for a, b in zip(segments, segments[1:]):
        if a["end"] != b["start"]:
            #print(f"Constraint violated: gap/overlap between {a} and {b}")
            return False, {"gap/overlap": (a, b)}

    # 2) check each place's stay duration
    for seg in segments:
        required = constraints.get("stay_days", {}).get(seg["place"])
        if required is not None:
            actual = seg["end"] - seg["start"] + 1
            if actual != required:
                print(f"Constraint violated: {seg['place']} stayed {actual} days, need {required}")
                return False, {"stay_days": {seg["place"]: required}}

    # 3) check event_ranges (must fall entirely within the visit segment)
    for ev in constraints.get("city_day_ranges", []):
        place = ev["city"]
        container = next((s for s in segments if s["place"] == place), None)
        if not container:
            print(f"Constraint violated: no segment for {place}")
            return False, {"missing_place": place}
        if container["start"] > ev["start"] or container["end"] < ev["end"]:
            print(f"Constraint violated: event {ev} not within {container}")
            return False, {"event_range": ev}

    # 4) check flight connectivity between consecutive places
    allowed = [(d["from"], d["to"]) for d in constraints.get("direct_flights")]
    for a, b in zip(segments, segments[1:]):
        pair = (a["place"], b["place"])
        if pair not in allowed:
            print(f"Constraint violated: no direct flight from {a['place']} to {b['place']}")
            return False, {"flight": {"from": a["place"], "to": b["place"]}}

    return True, {}

def evaluate_meeting(constraints, pred_dict):
    from datetime import datetime

    def parse_time(s):
        # handles "H:MM" or "H:MMAM"/"H:MMPM"
        if s.endswith(("AM", "PM")):
            return datetime.strptime(s, "%I:%M%p")
        return datetime.strptime(s, "%H:%M")

    # build map person→availability & location
    people = {p["name"]: p for p in constraints.get("people_to_meet", [])}
    start_location = constraints.get("start", {}).get("location")
    start_time = constraints.get("start", {}).get("time_of_day")
    num_people_to_meet = constraints.get("num_people_to_meet", 0)

    # parse predicted meetings
    meetings = []
    for m in pred_dict.get("itinerary", []):
        name = m["person"]
        start = parse_time(m["start_time"])
        end   = parse_time(m["end_time"])
        loc   = people.get(name, {}).get("location")
        meetings.append({"person": name, "start": start, "end": end, "location": loc})

    if len(meetings) < num_people_to_meet:
        return False, {"num_people_to_meet": num_people_to_meet}
    # sort chronologically
    meetings.sort(key=lambda x: x["start"])

    # 1) each meeting must lie within that person's available window
    for m in meetings:
        p = people.get(m["person"])
        if not p:
            continue
        avail = p["time_of_day"]
        av_from = parse_time(avail["from"])
        av_to   = parse_time(avail["to"])
        if m["start"] < av_from or m["end"] > av_to:
            return False, {"person": m["person"], "time_of_day": avail}

    # 2) build travel‐time lookup
    travel = {}
    for d in constraints.get("travel_distances", []):
        pl = d["place"]
        frm = pl.get("from", constraints.get("start", {}).get("location"))
        to  = pl["to"]
        travel[(frm, to)] = d["walking_time"]

    # 3) check start‐to‐first meeting
    # parse start time
    if start_time:
        st = parse_time(start_time)
        first = meetings[0]
        # 0a) meeting must not start before you arrive
        if first["start"] < st:
            return False, {"start_time": start_time}
        # 0b) travel from start_location
        walk0 = travel.get((start_location, first["location"]))
        gap0 = (first["start"] - st).total_seconds() / 60
        if walk0 is not None and walk0 > gap0:
            return False, {
                "travel_start": {
                    "to_person":   first["person"],
                    "to_location": first["location"],
                    "travel_time": walk0
                }
            }

    # 3) check following meetings
    for a, b in zip(meetings, meetings[1:]):
        gap_mins = (b["start"] - a["end"]).total_seconds() / 60
        walk     = travel.get((a["location"], b["location"]))
        if walk is not None and walk > gap_mins:
            return False, {
                "travel": {
                    "from_person": a["person"],
                    "to_person":   b["person"],
                    "from_location": a["location"],
                    "to_location":   b["location"],
                    "travel_time":   walk
                }
            }

    return True, {}

task_name_map = {
    "calendar": "calendar_scheduling",
    "trip": "trip_planning",
    "meeting": "meeting_planning"
}

task_function_map = {
    "calendar": evaluate_calendar,
    "trip": evaluate_trip,
    "meeting": evaluate_meeting
}

if args.task == "all":
    tasks = ["calendar", "trip", "meeting"]
else:
    tasks = [args.task]

model = args.model
for task in tasks:
    # Load constraints
    with open(f"../data/{task_name_map[task]}_100_constraints.json") as f:
        constraints_data = json.load(f)
        
    # Initialize evaluation results
    results = {
        "total": 0,
        "constraint_satisfied": 0
    }
    
    # Get the evaluation function for this task
    eval_func = task_function_map[task]
    if eval_func is None:
        print(f"Skipping {task} as evaluation function is not implemented")
        continue
        
    # Directory with formatted outputs
    if args.output == "plan":
        pass # TODO: fill in the path
    elif args.output == "python":
        pass # TODO: fill in the path
    elif args.output == "z3":
        output_dir = f"../output/SMT/{model}/{task}/formatted_output"
        report_path = f"../output/SMT/{model}/{task}/report.json"
    
    total_count = 0
    no_error_count = 0
    has_plan_count = 0
    correct_count = 0
    example_result = {}
    # Process each file
    for filename in os.listdir(output_dir):
        print(output_dir)
        with open(os.path.join(output_dir, filename), 'r') as f:
            output_data = json.load(f)
            
        example_id = filename.replace('.json', '')
        print(f"Processing example {example_id}")
        status = ""
        violated_constraint = {}
                
        # Extract prediction from the formatted output
        entry = output_data.get("0shot", [{}])[0]
        pred_dict = entry.get("final_program_time")
        gold_dict = entry.get("expected_time")
        total_count += 1
        if entry.get("has_error"):
            status = "Error"
        elif "itinerary" in pred_dict and not pred_dict["itinerary"] or not pred_dict:
            no_error_count += 1
            status = "No plan"
        else:
            no_error_count += 1
            has_plan_count += 1
            # Get constraints for this example
            example_constraints = constraints_data.get(example_id, {}).get("constraints", {})

            # Special handling for meeting
            if task == "meeting":
                itinerary = pred_dict.get("itinerary")
                itinerary = [{
                                "action": x["action"],
                                "person": x["person"],
                                "start_time": x["start_time"],
                                "end_time": x["end_time"]
                            } for x in itinerary]
                itinerary.sort(key=lambda x: x["start_time"])
                pred_dict = {"itinerary": itinerary}
                # For meeting, use the number of people to meet in the gold solution as a constraint
                num_people_to_meet = len(gold_dict.get("itinerary", []))
                example_constraints["num_people_to_meet"] = num_people_to_meet
            
            # Evaluate if prediction satisfies constraints
            is_pass, violated_constraint = eval_func(example_constraints, pred_dict)
            if is_pass:
                status = "Correct"
                correct_count += 1
            else:
                status = "Wrong plan"
        example_result[example_id] = {
            "pred": pred_dict,
            "gold": gold_dict,
            "status": status,
            "violated_constraint": violated_constraint,
            "is_exact_match": pred_dict == gold_dict,
            #"constraints": example_constraints,
        }
    
    report_data = {
        "total_examples": total_count,
        "no_error_examples": no_error_count,
        "has_plan_examples": has_plan_count,
        "correct_examples": correct_count,
        "result_by_example": example_result,
    }
    print("Total examples:", total_count)
    print("No error examples:", no_error_count)
    print("Has plan examples:", has_plan_count)
    print("Correct examples:", correct_count)
    with open(report_path, "w") as f:
        json.dump(report_data, f, indent=4)