"SOLUTION:"
import json
import itertools

# Helper functions
def to_minutes(h, m):
    return h * 60 + m

def fmt_minutes(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

# Input variables (constraints and travel times)
start_location = "Russian Hill"
start_time = to_minutes(9, 0)  # 9:00

travel = {
    "Russian Hill": {"Nob Hill": 5, "Mission District": 16, "Embarcadero": 8},
    "Nob Hill": {"Russian Hill": 5, "Mission District": 13, "Embarcadero": 9},
    "Mission District": {"Russian Hill": 15, "Nob Hill": 12, "Embarcadero": 19},
    "Embarcadero": {"Russian Hill": 8, "Nob Hill": 10, "Mission District": 20},
}

friends = {
    "Patricia": {
        "location": "Nob Hill",
        "window_start": to_minutes(18, 30),  # 18:30
        "window_end": to_minutes(21, 45),    # 21:45
        "min_duration": 90
    },
    "Ashley": {
        "location": "Mission District",
        "window_start": to_minutes(20, 30),  # 20:30
        "window_end": to_minutes(21, 15),    # 21:15
        "min_duration": 45
    },
    "Timothy": {
        "location": "Embarcadero",
        "window_start": to_minutes(9, 45),   # 9:45
        "window_end": to_minutes(17, 45),    # 17:45
        "min_duration": 120
    },
}

# Compute the best schedule:
# Objective: maximize number of friends met; tie-break by (1) minimal total travel time, (2) earliest finish time
friend_names = list(friends.keys())

def compute_schedule(order):
    cur_loc = start_location
    cur_time = start_time
    itinerary = []
    total_travel = 0

    for person in order:
        info = friends[person]
        loc = info["location"]
        # Travel
        t_travel = travel[cur_loc][loc]
        arrival = cur_time + t_travel
        total_travel += t_travel
        # Earliest feasible meeting start
        start_meet = max(arrival, info["window_start"])
        end_meet = start_meet + info["min_duration"]
        # Check feasibility within window
        if end_meet > info["window_end"]:
            return None  # infeasible
        # Record
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person,
            "start_time": fmt_minutes(start_meet),
            "end_time": fmt_minutes(end_meet),
        })
        # Update state
        cur_loc = loc
        cur_time = end_meet

    return {
        "itinerary": itinerary,
        "count": len(order),
        "total_travel": total_travel,
        "finish_time": cur_time
    }

best = None

# Try all subsets (by size descending), and all permutations within each subset
for k in range(len(friend_names), 0, -1):
    found_for_k = []
    for subset in itertools.combinations(friend_names, k):
        for perm in itertools.permutations(subset):
            sched = compute_schedule(perm)
            if sched:
                found_for_k.append(sched)
    if found_for_k:
        # Choose the best by tie-breakers
        # - minimal total_travel
        # - earliest finish_time
        found_for_k.sort(key=lambda s: (s["total_travel"], s["finish_time"]))
        best = found_for_k[0]
        break

# Fallback if none found (should not happen with provided constraints)
output = {"itinerary": []}
if best:
    output["itinerary"] = best["itinerary"]

print(json.dumps(output, ensure_ascii=False))