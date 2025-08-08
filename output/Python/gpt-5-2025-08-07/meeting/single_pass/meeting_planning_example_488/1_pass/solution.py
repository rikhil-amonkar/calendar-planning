import itertools
import json

def minutes(h, m):
    return h * 60 + m

def fmt_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

# Input variables (meeting constraints)
start_location = "Pacific Heights"
arrival_time = minutes(9, 0)

friends = [
    {"name": "Ronald", "location": "Nob Hill", "start": minutes(10, 0), "end": minutes(17, 0), "min_duration": 105},
    {"name": "Sarah", "location": "Russian Hill", "start": minutes(7, 15), "end": minutes(9, 30), "min_duration": 45},
    {"name": "Helen", "location": "The Castro", "start": minutes(13, 30), "end": minutes(17, 0), "min_duration": 120},
    {"name": "Joshua", "location": "Sunset District", "start": minutes(14, 15), "end": minutes(19, 30), "min_duration": 90},
    {"name": "Margaret", "location": "Haight-Ashbury", "start": minutes(10, 15), "end": minutes(22, 0), "min_duration": 60},
]

# Directed travel times (in minutes)
T = {
    "Pacific Heights": {
        "Nob Hill": 8,
        "Russian Hill": 7,
        "The Castro": 16,
        "Sunset District": 21,
        "Haight-Ashbury": 11,
    },
    "Nob Hill": {
        "Pacific Heights": 8,
        "Russian Hill": 5,
        "The Castro": 17,
        "Sunset District": 25,
        "Haight-Ashbury": 13,
    },
    "Russian Hill": {
        "Pacific Heights": 7,
        "Nob Hill": 5,
        "The Castro": 21,
        "Sunset District": 23,
        "Haight-Ashbury": 17,
    },
    "The Castro": {
        "Pacific Heights": 16,
        "Nob Hill": 16,
        "Russian Hill": 18,
        "Sunset District": 17,
        "Haight-Ashbury": 6,
    },
    "Sunset District": {
        "Pacific Heights": 21,
        "Nob Hill": 27,
        "Russian Hill": 24,
        "The Castro": 17,
        "Haight-Ashbury": 15,
    },
    "Haight-Ashbury": {
        "Pacific Heights": 12,
        "Nob Hill": 15,
        "Russian Hill": 17,
        "The Castro": 6,
        "Sunset District": 15,
    },
}

# Ensure travel times exist between any two distinct locations
locations = list(T.keys())
for a in locations:
    for b in locations:
        if a == b:
            continue
        if b not in T[a]:
            raise ValueError(f"Missing travel time from {a} to {b}")

def evaluate_order(order):
    current_time = arrival_time
    current_loc = start_location
    itinerary = []
    total_travel = 0

    for person in order:
        travel = T[current_loc][person["location"]]
        total_travel += travel
        arrival = current_time + travel
        start_meet = max(arrival, person["start"])
        end_meet = start_meet + person["min_duration"]
        if end_meet > person["end"]:
            return None  # infeasible
        itinerary.append({
            "action": "meet",
            "location": person["location"],
            "person": person["name"],
            "start_time": fmt_time(start_meet),
            "end_time": fmt_time(end_meet),
            "_start_min": start_meet,
            "_end_min": end_meet
        })
        current_time = end_meet
        current_loc = person["location"]

    return {
        "itinerary": itinerary,
        "count": len(order),
        "end_time": current_time,
        "travel_time": total_travel,
        "total_meet_time": sum(p["min_duration"] for p in order),
    }

def optimize_schedule(friends):
    best = None
    n = len(friends)
    # Consider all permutations of all non-empty subsets
    for k in range(n, 0, -1):
        found_better_in_k = False
        for subset in itertools.permutations(friends, k):
            result = evaluate_order(subset)
            if result is None:
                continue
            if best is None:
                best = result
                found_better_in_k = True
                continue
            # Primary: maximize count
            if result["count"] > best["count"]:
                best = result
                found_better_in_k = True
            elif result["count"] == best["count"]:
                # Secondary: earliest end time
                if result["end_time"] < best["end_time"]:
                    best = result
                    found_better_in_k = True
                elif result["end_time"] == best["end_time"]:
                    # Tertiary: minimize total travel time
                    if result["travel_time"] < best["travel_time"]:
                        best = result
                        found_better_in_k = True
                    elif result["travel_time"] == best["travel_time"]:
                        # Quaternary: maximize total meeting time (though identical for same people if using min durations)
                        if result["total_meet_time"] > best["total_meet_time"]:
                            best = result
                            found_better_in_k = True
        # If we found a feasible plan for this k (starting from largest), we can stop exploring smaller subsets
        if found_better_in_k:
            break
    return best

best_plan = optimize_schedule(friends)

# Prepare output JSON
output = {"itinerary": []}
if best_plan:
    # Strip helper fields before output
    for item in best_plan["itinerary"]:
        clean_item = {
            "action": item["action"],
            "location": item["location"],
            "person": item["person"],
            "start_time": item["start_time"],
            "end_time": item["end_time"],
        }
        output["itinerary"].append(clean_item)

print(json.dumps(output))