"""SOLUTION:"""
import itertools
import json

# Utility functions
def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Input variables (meeting constraints)
start_location = "Richmond District"
start_time = minutes(9, 0)

friends = {
    "Kimberly": {
        "location": "Marina District",
        "window_start": minutes(13, 15),
        "window_end": minutes(16, 45),
        "min_duration": 15
    },
    "Robert": {
        "location": "Chinatown",
        "window_start": minutes(12, 15),
        "window_end": minutes(20, 15),
        "min_duration": 15
    },
    "Rebecca": {
        "location": "Financial District",
        "window_start": minutes(13, 15),
        "window_end": minutes(16, 45),
        "min_duration": 75
    },
    "Margaret": {
        "location": "Bayview",
        "window_start": minutes(9, 30),
        "window_end": minutes(13, 30),
        "min_duration": 30
    },
    "Kenneth": {
        "location": "Union Square",
        "window_start": minutes(19, 30),
        "window_end": minutes(21, 15),
        "min_duration": 75
    },
}

# Travel times (in minutes) between locations
travel = {
    "Richmond District": {
        "Marina District": 9,
        "Chinatown": 20,
        "Financial District": 22,
        "Bayview": 26,
        "Union Square": 21,
    },
    "Marina District": {
        "Richmond District": 11,
        "Chinatown": 16,
        "Financial District": 17,
        "Bayview": 27,
        "Union Square": 16,
    },
    "Chinatown": {
        "Richmond District": 20,
        "Marina District": 12,
        "Financial District": 5,
        "Bayview": 22,
        "Union Square": 7,
    },
    "Financial District": {
        "Richmond District": 21,
        "Marina District": 15,
        "Chinatown": 5,
        "Bayview": 19,
        "Union Square": 9,
    },
    "Bayview": {
        "Richmond District": 25,
        "Marina District": 25,
        "Chinatown": 18,
        "Financial District": 19,
        "Union Square": 17,
    },
    "Union Square": {
        "Richmond District": 20,
        "Marina District": 18,
        "Chinatown": 7,
        "Financial District": 9,
        "Bayview": 15,
    },
}

def get_travel(a, b):
    if a == b:
        return 0
    return travel[a][b]

def simulate_order(order):
    itinerary = []
    current_loc = start_location
    current_time = start_time
    total_wait = 0
    total_travel = 0

    for person in order:
        info = friends[person]
        loc = info["location"]
        t_travel = get_travel(current_loc, loc)
        arrive = current_time + t_travel
        start = max(arrive, info["window_start"])
        end = start + info["min_duration"]
        if end > info["window_end"]:
            return None  # infeasible
        wait = max(0, start - arrive)
        total_wait += wait
        total_travel += t_travel
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person,
            "start_time": fmt_time(start),
            "end_time": fmt_time(end),
        })
        current_loc = loc
        current_time = end

    return {
        "itinerary": itinerary,
        "end_time": current_time,
        "total_wait": total_wait,
        "total_travel": total_travel
    }

# Optimize: maximize number of friends met; tie-break by minimal total waiting, then earliest end, then minimal travel.
friend_names = list(friends.keys())
best_plan = None
best_k = 0

for k in range(len(friend_names), 0, -1):
    candidate_best = None
    for order in itertools.permutations(friend_names, k):
        result = simulate_order(order)
        if result is None:
            continue
        score = (result["total_wait"], result["end_time"], result["total_travel"])
        if candidate_best is None or score < (candidate_best["total_wait"], candidate_best["end_time"], candidate_best["total_travel"]):
            candidate_best = result
    if candidate_best:
        best_plan = candidate_best
        best_k = k
        break

output = {"itinerary": best_plan["itinerary"] if best_plan else []}
print(json.dumps(output, ensure_ascii=False))