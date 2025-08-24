import itertools
import json

# Helper functions
def to_minutes(tstr):
    h, m = map(int, tstr.split(":"))
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables (meeting constraints)
start_location = "Presidio"
start_time_str = "9:00"

people = [
    {
        "name": "Jason",
        "location": "Richmond District",
        "window_start": "13:00",
        "window_end": "20:45",
        "min_duration_min": 90
    },
    {
        "name": "Melissa",
        "location": "North Beach",
        "window_start": "18:45",
        "window_end": "20:15",
        "min_duration_min": 45
    },
    {
        "name": "Brian",
        "location": "Financial District",
        "window_start": "9:45",
        "window_end": "21:45",
        "min_duration_min": 15
    },
    {
        "name": "Elizabeth",
        "location": "Golden Gate Park",
        "window_start": "8:45",
        "window_end": "21:30",
        "min_duration_min": 105
    },
    {
        "name": "Laura",
        "location": "Union Square",
        "window_start": "14:15",
        "window_end": "19:30",
        "min_duration_min": 75
    },
]

# Convert times to minutes for computation
for p in people:
    p["ws"] = to_minutes(p["window_start"])
    p["we"] = to_minutes(p["window_end"])
    p["dur"] = p["min_duration_min"]

start_time = to_minutes(start_time_str)

# Travel times in minutes between locations
travel = {
    "Presidio": {
        "Richmond District": 7,
        "North Beach": 18,
        "Financial District": 23,
        "Golden Gate Park": 12,
        "Union Square": 22
    },
    "Richmond District": {
        "Presidio": 7,
        "North Beach": 17,
        "Financial District": 22,
        "Golden Gate Park": 9,
        "Union Square": 21
    },
    "North Beach": {
        "Presidio": 17,
        "Richmond District": 18,
        "Financial District": 8,
        "Golden Gate Park": 22,
        "Union Square": 7
    },
    "Financial District": {
        "Presidio": 22,
        "Richmond District": 21,
        "North Beach": 7,
        "Golden Gate Park": 23,
        "Union Square": 9
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Richmond District": 7,
        "North Beach": 24,
        "Financial District": 26,
        "Union Square": 22
    },
    "Union Square": {
        "Presidio": 24,
        "Richmond District": 20,
        "North Beach": 10,
        "Financial District": 9,
        "Golden Gate Park": 22
    }
}

# Ensure travel times are accessible for all pairs used
locations = list(travel.keys())

def get_travel(a, b):
    if a == b:
        return 0
    return travel[a][b]

# Evaluate a specific ordered list of people, computing earliest-feasible schedule
def evaluate_order(order):
    current_loc = start_location
    current_time = start_time
    total_travel = 0
    schedule = []
    waiting = 0

    for p in order:
        t = get_travel(current_loc, p["location"])
        arrival = current_time + t
        start_mt = max(arrival, p["ws"])
        end_mt = start_mt + p["dur"]
        if end_mt > p["we"]:
            return None  # infeasible
        schedule.append({
            "person": p["name"],
            "location": p["location"],
            "start": start_mt,
            "end": end_mt
        })
        total_travel += t
        waiting += max(0, start_mt - arrival)
        current_loc = p["location"]
        current_time = end_mt

    finish_time = current_time
    total_meeting = sum(p["dur"] for p in order)
    idle_time = (finish_time - start_time) - total_travel - total_meeting

    return {
        "schedule": schedule,
        "count": len(order),
        "finish": finish_time,
        "travel": total_travel,
        "waiting": waiting,
        "idle": idle_time
    }

# Search over all subsets and permutations to maximize number of friends met
best = None

# Precompute all people indices for convenience
people_list = people

# Iterate over all subset sizes from largest to smallest to allow early pruning
for r in range(len(people_list), 0, -1):
    found_any = False
    for subset in itertools.combinations(people_list, r):
        for perm in itertools.permutations(subset):
            res = evaluate_order(perm)
            if res is None:
                continue
            found_any = True
            # Optimization criteria:
            # 1) Maximize count
            # 2) Minimize finish time
            # 3) Minimize total travel time
            # 4) Minimize idle time
            # 5) Minimize waiting time
            key = (
                -res["count"],
                res["finish"],
                res["travel"],
                res["idle"],
                res["waiting"]
            )
            if best is None or key < best["key"]:
                best = {"key": key, "result": res}
    if found_any:
        break  # we found at least one feasible schedule with r people; no need to try smaller r

# Build output JSON
output = {"itinerary": []}

if best:
    for item in best["result"]["schedule"]:
        output["itinerary"].append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": fmt_time(item["start"]),
            "end_time": fmt_time(item["end"])
        })

print(json.dumps(output, ensure_ascii=False))