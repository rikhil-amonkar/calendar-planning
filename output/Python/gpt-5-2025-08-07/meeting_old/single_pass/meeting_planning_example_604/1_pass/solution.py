import json
from itertools import permutations

def fmt_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

# Travel times (minutes) between locations (directional)
T = {
    "Fisherman's Wharf": {
        "The Castro": 26, "Golden Gate Park": 25, "Embarcadero": 8,
        "Russian Hill": 7, "Nob Hill": 11, "Alamo Square": 20, "North Beach": 6
    },
    "The Castro": {
        "Fisherman's Wharf": 24, "Golden Gate Park": 11, "Embarcadero": 22,
        "Russian Hill": 18, "Nob Hill": 16, "Alamo Square": 8, "North Beach": 20
    },
    "Golden Gate Park": {
        "Fisherman's Wharf": 24, "The Castro": 13, "Embarcadero": 25,
        "Russian Hill": 19, "Nob Hill": 20, "Alamo Square": 10, "North Beach": 24
    },
    "Embarcadero": {
        "Fisherman's Wharf": 6, "The Castro": 25, "Golden Gate Park": 25,
        "Russian Hill": 8, "Nob Hill": 10, "Alamo Square": 19, "North Beach": 5
    },
    "Russian Hill": {
        "Fisherman's Wharf": 7, "The Castro": 21, "Golden Gate Park": 21,
        "Embarcadero": 8, "Nob Hill": 5, "Alamo Square": 15, "North Beach": 5
    },
    "Nob Hill": {
        "Fisherman's Wharf": 11, "The Castro": 17, "Golden Gate Park": 17,
        "Embarcadero": 9, "Russian Hill": 5, "Alamo Square": 11, "North Beach": 8
    },
    "Alamo Square": {
        "Fisherman's Wharf": 19, "The Castro": 8, "Golden Gate Park": 9,
        "Embarcadero": 17, "Russian Hill": 13, "Nob Hill": 11, "North Beach": 15
    },
    "North Beach": {
        "Fisherman's Wharf": 5, "The Castro": 22, "Golden Gate Park": 22,
        "Embarcadero": 6, "Russian Hill": 4, "Nob Hill": 7, "Alamo Square": 16
    },
}

# Meeting constraints
friends = {
    "Laura": {
        "location": "The Castro",
        "start": 19*60 + 45,   # 19:45
        "end": 21*60 + 30,     # 21:30
        "min_dur": 105
    },
    "Daniel": {
        "location": "Golden Gate Park",
        "start": 21*60 + 15,   # 21:15
        "end": 21*60 + 45,     # 21:45
        "min_dur": 15
    },
    "William": {
        "location": "Embarcadero",
        "start": 7*60 + 0,     # 7:00
        "end": 9*60 + 0,       # 9:00
        "min_dur": 90
    },
    "Karen": {
        "location": "Russian Hill",
        "start": 14*60 + 30,   # 14:30
        "end": 19*60 + 45,     # 19:45
        "min_dur": 30
    },
    "Stephanie": {
        "location": "Nob Hill",
        "start": 7*60 + 30,    # 7:30
        "end": 9*60 + 30,      # 9:30
        "min_dur": 45
    },
    "Joseph": {
        "location": "Alamo Square",
        "start": 11*60 + 30,   # 11:30
        "end": 12*60 + 45,     # 12:45
        "min_dur": 15
    },
    "Kimberly": {
        "location": "North Beach",
        "start": 15*60 + 45,   # 15:45
        "end": 19*60 + 15,     # 19:15
        "min_dur": 30
    },
}

start_location = "Fisherman's Wharf"
start_time = 9*60  # 9:00

# Helper to attempt scheduling a sequence in the given order using earliest-feasible starts
def schedule_sequence(order):
    current_loc = start_location
    current_time = start_time
    itinerary = []
    total_travel = 0
    total_wait = 0

    for name in order:
        info = friends[name]
        loc = info["location"]
        travel = T[current_loc][loc]
        earliest_arrival = current_time + travel
        start = max(earliest_arrival, info["start"])
        end = start + info["min_dur"]
        if end > info["end"]:
            return None  # infeasible for this order
        # accumulate travel and wait (idle) time since last meeting end
        total_travel += travel
        wait = max(0, start - earliest_arrival)
        total_wait += wait
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": fmt_time(start),
            "end_time": fmt_time(end),
            "_start": start,
            "_end": end,
            "_loc": loc
        })
        current_loc = loc
        current_time = end

    return {
        "itinerary": itinerary,
        "end_time": current_time,
        "total_travel": total_travel,
        "total_wait": total_wait
    }

# Backtracking search over all subsets and orders to maximize number of friends met
names = list(friends.keys())

best_plan = None

# Generate all permutations of all subset sizes (1..N)
# We will try a heuristic ordering to find good solutions early:
# sort friends by window end time ascending to reach good feasibility earlier
def window_end(name):
    return friends[name]["end"]
names_sorted = sorted(names, key=window_end)

from itertools import combinations

N = len(names)
for k in range(N, 0, -1):  # try larger cardinalities first
    found_any = False
    # combinations of size k
    for subset in combinations(names_sorted, k):
        # try all permutations of this subset; prioritize by earliest window end ordering
        # but permutations inherently vary; to keep deterministic, we can use permutations of subset as given
        for order in permutations(subset):
            plan = schedule_sequence(order)
            if plan is None:
                continue
            # filter out meetings that are impossible given arrival time at day start (sanity)
            # Already ensured by schedule_sequence.
            if best_plan is None:
                best_plan = plan
                found_any = True
            else:
                # Compare: maximize number met (same k), then minimize total_wait, then minimize total_travel, then earlier end_time
                if len(plan["itinerary"]) > len(best_plan["itinerary"]):
                    best_plan = plan
                    found_any = True
                elif len(plan["itinerary"]) == len(best_plan["itinerary"]):
                    if plan["total_wait"] < best_plan["total_wait"]:
                        best_plan = plan
                        found_any = True
                    elif plan["total_wait"] == best_plan["total_wait"]:
                        if plan["total_travel"] < best_plan["total_travel"]:
                            best_plan = plan
                            found_any = True
                        elif plan["total_travel"] == best_plan["total_travel"]:
                            if plan["end_time"] < best_plan["end_time"]:
                                best_plan = plan
                                found_any = True
    if found_any:
        break  # we found at least one schedule with k meetings, no need to try smaller k

# Produce final itinerary in required JSON format (without internal helper fields)
output = {"itinerary": []}
if best_plan:
    for item in best_plan["itinerary"]:
        output["itinerary"].append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": item["start_time"],
            "end_time": item["end_time"]
        })

print(json.dumps(output, ensure_ascii=False))