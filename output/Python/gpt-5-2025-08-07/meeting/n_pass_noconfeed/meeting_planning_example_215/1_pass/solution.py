"SOLUTION:"

import json
from itertools import combinations, permutations

# Input parameters
start_location = "Bayview"
start_time_str = "9:00"

# Travel times (directed, in minutes)
travel = {
    "Bayview": {
        "Embarcadero": 19,
        "Richmond District": 25,
        "Fisherman's Wharf": 25,
    },
    "Embarcadero": {
        "Bayview": 21,
        "Richmond District": 21,
        "Fisherman's Wharf": 6,
    },
    "Richmond District": {
        "Bayview": 26,
        "Embarcadero": 19,
        "Fisherman's Wharf": 18,
    },
    "Fisherman's Wharf": {
        "Bayview": 26,
        "Embarcadero": 8,
        "Richmond District": 18,
    },
}

# Participants and constraints
people = {
    "Jessica": {
        "location": "Embarcadero",
        "window_start": "16:45",
        "window_end": "19:00",
        "min_duration": 30,
    },
    "Sandra": {
        "location": "Richmond District",
        "window_start": "18:30",
        "window_end": "21:45",
        "min_duration": 120,
    },
    "Jason": {
        "location": "Fisherman's Wharf",
        "window_start": "16:00",
        "window_end": "16:45",
        "min_duration": 30,
    },
}

def parse_time(tstr):
    h, m = tstr.split(":")
    return int(h) * 60 + int(m)

def fmt_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Convert input times to minutes
start_time = parse_time(start_time_str)
for p in people.values():
    p["win_start_min"] = parse_time(p["window_start"])
    p["win_end_min"] = parse_time(p["window_end"])

names = list(people.keys())

def attempt_schedule(order):
    itinerary = []
    current_loc = start_location
    current_time = start_time
    total_travel = 0
    total_wait = 0
    total_meeting = 0

    for name in order:
        info = people[name]
        dest = info["location"]
        if current_loc not in travel or dest not in travel[current_loc]:
            return None  # missing travel path

        ttime = travel[current_loc][dest]
        arrival = current_time + ttime
        start_meet = max(arrival, info["win_start_min"])
        end_meet = start_meet + info["min_duration"]

        # Infeasible if past window
        if end_meet > info["win_end_min"]:
            return None

        # Accumulate metrics
        total_travel += ttime
        wait = max(0, start_meet - arrival)
        total_wait += wait
        total_meeting += info["min_duration"]

        itinerary.append({
            "action": "meet",
            "location": dest,
            "person": name,
            "start_time": fmt_time(start_meet),
            "end_time": fmt_time(end_meet),
        })

        # Move to next
        current_loc = dest
        current_time = end_meet

    finish_time = current_time
    metrics = {
        "meetings": len(order),
        "total_meeting": total_meeting,
        "finish_time": finish_time,
        "total_travel": total_travel,
        "total_wait": total_wait,
    }
    return itinerary, metrics

best_plan = None
best_key = None

# Explore all subsets (largest first) and all orders
for size in range(len(names), 0, -1):
    for subset in combinations(names, size):
        for order in permutations(subset):
            res = attempt_schedule(order)
            if not res:
                continue
            itinerary, metrics = res
            # Objective: maximize number of meetings, then total meeting time,
            # then earliest finish time, then minimal total travel, then minimal total wait.
            key = (
                metrics["meetings"],
                metrics["total_meeting"],
                -metrics["finish_time"],
                -metrics["total_travel"],
                -metrics["total_wait"],
            )
            if (best_key is None) or (key > best_key):
                best_key = key
                best_plan = itinerary
    if best_plan:
        # Found a feasible plan with this number of meetings; no need to try smaller subsets
        break

output = {"itinerary": best_plan if best_plan else []}
print(json.dumps(output, ensure_ascii=False))