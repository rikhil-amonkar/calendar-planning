# SOLUTION:
import itertools
import json

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables (constraints and travel times)

start_location = "Sunset District"
start_time = 9 * 60  # 9:00

# Friends' availability and meeting requirements
friends = [
    {
        "name": "Charles",
        "location": "Alamo Square",
        "start": 18 * 60,       # 18:00
        "end": 20 * 60 + 45,    # 20:45
        "min_dur": 90
    },
    {
        "name": "Margaret",
        "location": "Russian Hill",
        "start": 9 * 60,        # 9:00
        "end": 16 * 60,         # 16:00
        "min_dur": 30
    },
    {
        "name": "Daniel",
        "location": "Golden Gate Park",
        "start": 8 * 60,        # 8:00
        "end": 13 * 60 + 30,    # 13:30
        "min_dur": 15
    },
    {
        "name": "Stephanie",
        "location": "Mission District",
        "start": 20 * 60 + 30,  # 20:30
        "end": 22 * 60,         # 22:00
        "min_dur": 90
    },
]

# Directed travel times in minutes
travel = {
    "Sunset District": {
        "Alamo Square": 17,
        "Russian Hill": 24,
        "Golden Gate Park": 11,
        "Mission District": 24
    },
    "Alamo Square": {
        "Sunset District": 16,
        "Russian Hill": 13,
        "Golden Gate Park": 9,
        "Mission District": 10
    },
    "Russian Hill": {
        "Sunset District": 23,
        "Alamo Square": 15,
        "Golden Gate Park": 21,
        "Mission District": 16
    },
    "Golden Gate Park": {
        "Sunset District": 10,
        "Alamo Square": 10,
        "Russian Hill": 19,
        "Mission District": 17
    },
    "Mission District": {
        "Sunset District": 24,
        "Alamo Square": 11,
        "Russian Hill": 15,
        "Golden Gate Park": 17
    }
}

def simulate_schedule(order):
    itinerary = []
    current_loc = start_location
    current_time = start_time
    total_travel = 0
    total_idle = 0

    for friend in order:
        loc = friend["location"]
        if current_loc not in travel or loc not in travel[current_loc]:
            return None  # missing travel path
        t_travel = travel[current_loc][loc]
        total_travel += t_travel
        arrival = current_time + t_travel
        start_meet = max(arrival, friend["start"])
        idle = max(0, start_meet - arrival)
        total_idle += idle
        end_meet = start_meet + friend["min_dur"]
        if end_meet > friend["end"]:
            return None  # infeasible due to availability
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": friend["name"],
            "start_time": fmt_time(start_meet),
            "end_time": fmt_time(end_meet),
            "_start_min": start_meet,
            "_end_min": end_meet
        })
        current_loc = loc
        current_time = end_meet

    finish_time = current_time
    return {
        "itinerary": itinerary,
        "total_travel": total_travel,
        "total_idle": total_idle,
        "finish_time": finish_time,
        "count": len(order)
    }

def choose_best_schedule(friends):
    best = None
    n = len(friends)
    # Enumerate all non-empty subsets and all permutations within each subset
    for r in range(1, n + 1):
        for subset in itertools.combinations(friends, r):
            for order in itertools.permutations(subset):
                result = simulate_schedule(order)
                if result is None:
                    continue
                score = (
                    -result["count"],           # maximize number of friends
                    result["total_idle"],       # minimize idle time
                    result["total_travel"],     # minimize travel
                    result["finish_time"]       # minimize finish time
                )
                if best is None or score < best["score"]:
                    best = {
                        "score": score,
                        "result": result
                    }
    return best["result"] if best else None

best_schedule = choose_best_schedule(friends)

# Prepare final JSON output
output = {"itinerary": []}
if best_schedule:
    # Strip internal fields
    for item in best_schedule["itinerary"]:
        output["itinerary"].append({
            "action": item["action"],
            "location": item["location"],
            "person": item["person"],
            "start_time": item["start_time"],
            "end_time": item["end_time"]
        })

print(json.dumps(output, ensure_ascii=False))