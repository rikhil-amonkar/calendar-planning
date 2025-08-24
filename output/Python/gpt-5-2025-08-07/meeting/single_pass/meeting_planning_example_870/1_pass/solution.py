# SOLUTION:
import itertools
import json

# Time helpers
def minutes(h, m):
    return h * 60 + m

def to_str_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Input variables
start_location = "Pacific Heights"
start_time = minutes(9, 0)

# Travel times (directed, in minutes)
travel = {
    "Pacific Heights": {
        "Marina District": 6,
        "The Castro": 16,
        "Richmond District": 12,
        "Alamo Square": 10,
        "Financial District": 13,
        "Presidio": 11,
        "Mission District": 15,
        "Nob Hill": 8,
        "Russian Hill": 7,
    },
    "Marina District": {
        "Pacific Heights": 7,
        "The Castro": 22,
        "Richmond District": 11,
        "Alamo Square": 15,
        "Financial District": 17,
        "Presidio": 10,
        "Mission District": 20,
        "Nob Hill": 12,
        "Russian Hill": 8,
    },
    "The Castro": {
        "Pacific Heights": 16,
        "Marina District": 21,
        "Richmond District": 16,
        "Alamo Square": 8,
        "Financial District": 21,
        "Presidio": 20,
        "Mission District": 7,
        "Nob Hill": 16,
        "Russian Hill": 18,
    },
    "Richmond District": {
        "Pacific Heights": 10,
        "Marina District": 9,
        "The Castro": 16,
        "Alamo Square": 13,
        "Financial District": 22,
        "Presidio": 7,
        "Mission District": 20,
        "Nob Hill": 17,
        "Russian Hill": 13,
    },
    "Alamo Square": {
        "Pacific Heights": 10,
        "Marina District": 15,
        "The Castro": 8,
        "Richmond District": 11,
        "Financial District": 17,
        "Presidio": 17,
        "Mission District": 10,
        "Nob Hill": 11,
        "Russian Hill": 13,
    },
    "Financial District": {
        "Pacific Heights": 13,
        "Marina District": 15,
        "The Castro": 20,
        "Richmond District": 21,
        "Alamo Square": 17,
        "Presidio": 22,
        "Mission District": 17,
        "Nob Hill": 8,
        "Russian Hill": 11,
    },
    "Presidio": {
        "Pacific Heights": 11,
        "Marina District": 11,
        "The Castro": 21,
        "Richmond District": 7,
        "Alamo Square": 19,
        "Financial District": 23,
        "Mission District": 26,
        "Nob Hill": 18,
        "Russian Hill": 14,
    },
    "Mission District": {
        "Pacific Heights": 16,
        "Marina District": 19,
        "The Castro": 7,
        "Richmond District": 20,
        "Alamo Square": 11,
        "Financial District": 15,
        "Presidio": 25,
        "Nob Hill": 12,
        "Russian Hill": 15,
    },
    "Nob Hill": {
        "Pacific Heights": 8,
        "Marina District": 11,
        "The Castro": 17,
        "Richmond District": 14,
        "Alamo Square": 11,
        "Financial District": 9,
        "Presidio": 17,
        "Mission District": 13,
        "Russian Hill": 5,
    },
    "Russian Hill": {
        "Pacific Heights": 7,
        "Marina District": 7,
        "The Castro": 21,
        "Richmond District": 14,
        "Alamo Square": 15,
        "Financial District": 11,
        "Presidio": 14,
        "Mission District": 16,
        "Nob Hill": 5,
    },
}

# Friends' availability and minimum meeting durations
friends = [
    {"name": "Linda", "location": "Marina District", "start": minutes(18, 0), "end": minutes(22, 0), "min_duration": 30},
    {"name": "Kenneth", "location": "The Castro", "start": minutes(14, 45), "end": minutes(16, 15), "min_duration": 30},
    {"name": "Kimberly", "location": "Richmond District", "start": minutes(14, 15), "end": minutes(22, 0), "min_duration": 30},
    {"name": "Paul", "location": "Alamo Square", "start": minutes(21, 0), "end": minutes(21, 30), "min_duration": 15},
    {"name": "Carol", "location": "Financial District", "start": minutes(10, 15), "end": minutes(12, 0), "min_duration": 60},
    {"name": "Brian", "location": "Presidio", "start": minutes(10, 0), "end": minutes(21, 30), "min_duration": 75},
    {"name": "Laura", "location": "Mission District", "start": minutes(16, 15), "end": minutes(20, 30), "min_duration": 30},
    {"name": "Sandra", "location": "Nob Hill", "start": minutes(9, 15), "end": minutes(18, 30), "min_duration": 60},
    {"name": "Karen", "location": "Russian Hill", "start": minutes(18, 30), "end": minutes(22, 0), "min_duration": 75},
]

# Simulation to compute a feasible schedule (as subsequence) for a given permutation
def simulate_schedule(order):
    current_time = start_time
    current_loc = start_location
    itinerary = []
    total_travel = 0
    total_wait = 0

    for person in order:
        origin = current_loc
        dest = person["location"]
        # Ensure travel time exists
        if origin == dest:
            travel_time = 0
        else:
            if origin not in travel or dest not in travel[origin]:
                # If travel not defined, skip this person
                continue
            travel_time = travel[origin][dest]
        arrival = current_time + travel_time
        start_meet = max(arrival, person["start"])
        wait = max(0, start_meet - arrival)
        end_meet = start_meet + person["min_duration"]

        if end_meet <= person["end"]:
            itinerary.append({
                "action": "meet",
                "location": dest,
                "person": person["name"],
                "start_time": to_str_time(start_meet),
                "end_time": to_str_time(end_meet),
            })
            current_time = end_meet
            current_loc = dest
            total_travel += travel_time
            total_wait += wait
        else:
            # Skip this person (do not move)
            continue

    return {
        "itinerary": itinerary,
        "finish_time": current_time if itinerary else start_time,
        "total_travel": total_travel,
        "total_wait": total_wait,
        "count": len(itinerary),
    }

def better(plan_a, plan_b):
    # Return True if plan_a is better than plan_b
    if plan_a["count"] != plan_b["count"]:
        return plan_a["count"] > plan_b["count"]
    if plan_a["finish_time"] != plan_b["finish_time"]:
        return plan_a["finish_time"] < plan_b["finish_time"]
    if plan_a["total_wait"] != plan_b["total_wait"]:
        return plan_a["total_wait"] < plan_b["total_wait"]
    if plan_a["total_travel"] != plan_b["total_travel"]:
        return plan_a["total_travel"] < plan_b["total_travel"]
    return False

# Explore various schedules (all permutations, skipping infeasible meetings)
best_plan = {"itinerary": [], "finish_time": float("inf"), "total_travel": float("inf"), "total_wait": float("inf"), "count": 0}

for perm in itertools.permutations(friends):
    plan = simulate_schedule(perm)
    if better(plan, best_plan):
        best_plan = plan
        # Early exit if we met everyone
        if best_plan["count"] == len(friends):
            # Can't do better than meeting all friends
            # But continue a bit to ensure earliest finish if multiple; optional optimization:
            pass

# Output as JSON
output = {"itinerary": best_plan["itinerary"]}
print(json.dumps(output, ensure_ascii=False))