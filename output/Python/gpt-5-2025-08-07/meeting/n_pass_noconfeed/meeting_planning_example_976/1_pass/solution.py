import json
from copy import deepcopy

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Travel times (minutes)
travel = {
    "Embarcadero": {
        "Bayview": 21, "Chinatown": 7, "Alamo Square": 19, "Nob Hill": 10, "Presidio": 20,
        "Union Square": 10, "The Castro": 25, "North Beach": 5, "Fisherman's Wharf": 6, "Marina District": 12
    },
    "Bayview": {
        "Embarcadero": 19, "Chinatown": 19, "Alamo Square": 16, "Nob Hill": 20, "Presidio": 32,
        "Union Square": 18, "The Castro": 19, "North Beach": 22, "Fisherman's Wharf": 25, "Marina District": 27
    },
    "Chinatown": {
        "Embarcadero": 5, "Bayview": 20, "Alamo Square": 17, "Nob Hill": 9, "Presidio": 19,
        "Union Square": 7, "The Castro": 22, "North Beach": 3, "Fisherman's Wharf": 8, "Marina District": 12
    },
    "Alamo Square": {
        "Embarcadero": 16, "Bayview": 16, "Chinatown": 15, "Nob Hill": 11, "Presidio": 17,
        "Union Square": 14, "The Castro": 8, "North Beach": 15, "Fisherman's Wharf": 19, "Marina District": 15
    },
    "Nob Hill": {
        "Embarcadero": 9, "Bayview": 19, "Chinatown": 6, "Alamo Square": 11, "Presidio": 17,
        "Union Square": 7, "The Castro": 17, "North Beach": 8, "Fisherman's Wharf": 10, "Marina District": 11
    },
    "Presidio": {
        "Embarcadero": 20, "Bayview": 31, "Chinatown": 21, "Alamo Square": 19, "Nob Hill": 18,
        "Union Square": 22, "The Castro": 21, "North Beach": 18, "Fisherman's Wharf": 19, "Marina District": 11
    },
    "Union Square": {
        "Embarcadero": 11, "Bayview": 15, "Chinatown": 7, "Alamo Square": 15, "Nob Hill": 9,
        "Presidio": 24, "The Castro": 17, "North Beach": 10, "Fisherman's Wharf": 15, "Marina District": 18
    },
    "The Castro": {
        "Embarcadero": 22, "Bayview": 19, "Chinatown": 22, "Alamo Square": 8, "Nob Hill": 16,
        "Presidio": 20, "Union Square": 19, "North Beach": 20, "Fisherman's Wharf": 24, "Marina District": 21
    },
    "North Beach": {
        "Embarcadero": 6, "Bayview": 25, "Chinatown": 6, "Alamo Square": 16, "Nob Hill": 7,
        "Presidio": 17, "Union Square": 7, "The Castro": 23, "Fisherman's Wharf": 5, "Marina District": 9
    },
    "Fisherman's Wharf": {
        "Embarcadero": 8, "Bayview": 26, "Chinatown": 12, "Alamo Square": 21, "Nob Hill": 11,
        "Presidio": 17, "Union Square": 13, "The Castro": 27, "North Beach": 6, "Marina District": 9
    },
    "Marina District": {
        "Embarcadero": 14, "Bayview": 27, "Chinatown": 15, "Alamo Square": 15, "Nob Hill": 12,
        "Presidio": 10, "Union Square": 16, "The Castro": 22, "North Beach": 11, "Fisherman's Wharf": 10
    }
}

# Ensure self travel is 0 and symmetric dictionary access won't fail
locations = list(travel.keys())
for a in locations:
    travel[a][a] = 0

def get_travel(a, b):
    if a == b:
        return 0
    return travel[a][b]

# Friends constraints
friends = [
    # name, location, start_min, end_min, min_duration
    {"name": "Matthew", "location": "Bayview", "start": minutes(19, 15), "end": minutes(22, 0), "duration": 120},
    {"name": "Karen", "location": "Chinatown", "start": minutes(19, 15), "end": minutes(21, 15), "duration": 90},
    {"name": "Sarah", "location": "Alamo Square", "start": minutes(20, 0), "end": minutes(21, 45), "duration": 105},
    {"name": "Jessica", "location": "Nob Hill", "start": minutes(16, 30), "end": minutes(18, 45), "duration": 120},
    {"name": "Stephanie", "location": "Presidio", "start": minutes(7, 30), "end": minutes(10, 15), "duration": 60},
    {"name": "Mary", "location": "Union Square", "start": minutes(16, 45), "end": minutes(21, 30), "duration": 60},
    {"name": "Charles", "location": "The Castro", "start": minutes(16, 30), "end": minutes(22, 0), "duration": 105},
    {"name": "Nancy", "location": "North Beach", "start": minutes(14, 45), "end": minutes(20, 0), "duration": 15},
    {"name": "Thomas", "location": "Fisherman's Wharf", "start": minutes(13, 30), "end": minutes(19, 0), "duration": 30},
    {"name": "Brian", "location": "Marina District", "start": minutes(12, 15), "end": minutes(18, 0), "duration": 60},
]

# Precompute latest start times for pruning and ordering
for f in friends:
    f["latest_start"] = f["end"] - f["duration"]

start_location = "Embarcadero"
start_time = minutes(9, 0)

best_solution = {
    "count": 0,
    "end_time": float('inf'),
    "itinerary": []
}

# Simple memoization: (frozenset(met_names), location, time_rounded) -> best_count achieved
memo = {}

def optimistic_upper_bound(current_time, remaining):
    # Upper bound: count how many remaining friends could still be started if we magically teleport (no travel)
    cnt = 0
    for f in remaining:
        if current_time <= f["latest_start"]:
            cnt += 1
    return cnt

def dfs(current_loc, current_time, remaining, path, met_count):
    global best_solution

    # Branch and bound
    ub = met_count + optimistic_upper_bound(current_time, remaining)
    if ub < best_solution["count"]:
        return

    # Memoization key
    key = (frozenset([p["name"] for p in path]), current_loc, current_time // 1)
    prev_best = memo.get(key)
    if prev_best is not None and prev_best >= met_count:
        return
    memo[key] = met_count

    # Update best solution
    if met_count > best_solution["count"] or (met_count == best_solution["count"] and current_time < best_solution["end_time"]):
        best_solution = {
            "count": met_count,
            "end_time": current_time,
            "itinerary": deepcopy(path)
        }

    # Candidate next friends (feasible)
    candidates = []
    for f in remaining:
        travel_time = get_travel(current_loc, f["location"])
        arrival = current_time + travel_time
        # earliest feasible start
        start = max(arrival, f["start"])
        if start <= f["latest_start"]:
            end = start + f["duration"]
            candidates.append((f, start, end))

    # Sort candidates by earliest latest_start (deadline), then by start time
    candidates.sort(key=lambda x: (x[0]["latest_start"], x[1]))

    for f, start, end in candidates:
        new_path = path + [{
            "action": "meet",
            "location": f["location"],
            "person": f["name"],
            "start_time": start,
            "end_time": end
        }]
        new_remaining = [r for r in remaining if r["name"] != f["name"]]
        dfs(f["location"], end, new_remaining, new_path, met_count + 1)

# Start search
dfs(start_location, start_time, friends, [], 0)

# Format itinerary times
output_itinerary = []
for item in best_solution["itinerary"]:
    output_itinerary.append({
        "action": item["action"],
        "location": item["location"],
        "person": item["person"],
        "start_time": fmt_time(item["start_time"]),
        "end_time": fmt_time(item["end_time"])
    })

result = {"itinerary": output_itinerary}
print(json.dumps(result, ensure_ascii=False, indent=2))