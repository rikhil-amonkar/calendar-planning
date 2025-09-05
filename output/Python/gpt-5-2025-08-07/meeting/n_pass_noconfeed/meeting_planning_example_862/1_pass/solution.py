# SOLUTION:
import json

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Travel times (minutes) between neighborhoods
travel = {
    "Mission District": {
        "Alamo Square": 11, "Presidio": 25, "Russian Hill": 15, "North Beach": 17,
        "Golden Gate Park": 17, "Richmond District": 20, "Embarcadero": 19,
        "Financial District": 15, "Marina District": 19
    },
    "Alamo Square": {
        "Mission District": 10, "Presidio": 17, "Russian Hill": 13, "North Beach": 15,
        "Golden Gate Park": 9, "Richmond District": 11, "Embarcadero": 16,
        "Financial District": 17, "Marina District": 15
    },
    "Presidio": {
        "Mission District": 26, "Alamo Square": 19, "Russian Hill": 14, "North Beach": 18,
        "Golden Gate Park": 12, "Richmond District": 7, "Embarcadero": 20,
        "Financial District": 23, "Marina District": 11
    },
    "Russian Hill": {
        "Mission District": 16, "Alamo Square": 15, "Presidio": 14, "North Beach": 5,
        "Golden Gate Park": 21, "Richmond District": 14, "Embarcadero": 8,
        "Financial District": 11, "Marina District": 7
    },
    "North Beach": {
        "Mission District": 18, "Alamo Square": 16, "Presidio": 17, "Russian Hill": 4,
        "Golden Gate Park": 22, "Richmond District": 18, "Embarcadero": 6,
        "Financial District": 8, "Marina District": 9
    },
    "Golden Gate Park": {
        "Mission District": 17, "Alamo Square": 9, "Presidio": 11, "Russian Hill": 19,
        "North Beach": 23, "Richmond District": 7, "Embarcadero": 25,
        "Financial District": 26, "Marina District": 16
    },
    "Richmond District": {
        "Mission District": 20, "Alamo Square": 13, "Presidio": 7, "Russian Hill": 13,
        "North Beach": 17, "Golden Gate Park": 9, "Embarcadero": 19,
        "Financial District": 22, "Marina District": 9
    },
    "Embarcadero": {
        "Mission District": 20, "Alamo Square": 19, "Presidio": 20, "Russian Hill": 8,
        "North Beach": 5, "Golden Gate Park": 25, "Richmond District": 21,
        "Financial District": 5, "Marina District": 12
    },
    "Financial District": {
        "Mission District": 17, "Alamo Square": 17, "Presidio": 22, "Russian Hill": 11,
        "North Beach": 7, "Golden Gate Park": 23, "Richmond District": 21,
        "Embarcadero": 4, "Marina District": 15
    },
    "Marina District": {
        "Mission District": 20, "Alamo Square": 15, "Presidio": 10, "Russian Hill": 8,
        "North Beach": 11, "Golden Gate Park": 18, "Richmond District": 11,
        "Embarcadero": 14, "Financial District": 17
    }
}

# People constraints
people = [
    {
        "person": "Laura",
        "location": "Alamo Square",
        "start": minutes(14, 30),
        "end": minutes(16, 15),
        "min_duration": 75
    },
    {
        "person": "Brian",
        "location": "Presidio",
        "start": minutes(10, 15),
        "end": minutes(17, 0),
        "min_duration": 30
    },
    {
        "person": "Karen",
        "location": "Russian Hill",
        "start": minutes(18, 0),
        "end": minutes(20, 15),
        "min_duration": 90
    },
    {
        "person": "Stephanie",
        "location": "North Beach",
        "start": minutes(10, 15),
        "end": minutes(16, 0),
        "min_duration": 75
    },
    {
        "person": "Helen",
        "location": "Golden Gate Park",
        "start": minutes(11, 30),
        "end": minutes(21, 45),
        "min_duration": 120
    },
    {
        "person": "Sandra",
        "location": "Richmond District",
        "start": minutes(8, 0),
        "end": minutes(15, 15),
        "min_duration": 30
    },
    {
        "person": "Mary",
        "location": "Embarcadero",
        "start": minutes(16, 45),
        "end": minutes(18, 45),
        "min_duration": 120
    },
    {
        "person": "Deborah",
        "location": "Financial District",
        "start": minutes(19, 0),
        "end": minutes(20, 45),
        "min_duration": 105
    },
    {
        "person": "Elizabeth",
        "location": "Marina District",
        "start": minutes(8, 30),
        "end": minutes(13, 15),
        "min_duration": 105
    },
]

name_to_idx = {p["person"]: i for i, p in enumerate(people)}

start_location = "Mission District"
start_time = minutes(9, 0)

# Pre-calc window lengths for quick checks
for p in people:
    p["window_length"] = p["end"] - p["start"]

# Sort candidates by (end time, start time) for deterministic exploration
sorted_indices = sorted(range(len(people)), key=lambda i: (people[i]["end"], people[i]["start"]))

best_solution = {
    "count": 0,
    "total_meet": 0,
    "end_time": start_time,
    "total_travel": 0,
    "path": []
}

from functools import lru_cache

def feasible_next(current_loc, current_time, idx):
    p = people[idx]
    loc = p["location"]
    # Travel time from current_loc to loc
    t_travel = travel[current_loc][loc] if current_loc in travel and loc in travel[current_loc] else None
    if t_travel is None:
        return None
    arrival = current_time + t_travel
    start = max(arrival, p["start"])
    # Must be able to fit at least min_duration
    if start + p["min_duration"] > p["end"]:
        return None
    # For windows where min == window length, enforce start == window start (implicitly handled by previous check)
    duration = p["min_duration"]
    end = start + duration
    return (start, end, t_travel, duration)

def upper_bound_possible(current_time, remaining_set):
    # very loose bound: count how many people have any time left at or after current_time ignoring travel
    c = 0
    for idx in remaining_set:
        p = people[idx]
        latest_start = p["end"] - p["min_duration"]
        if current_time <= p["end"] and current_time <= latest_start or current_time <= p["start"] <= latest_start:
            c += 1
    return c

def dfs(current_loc, current_time, remaining, path, total_travel, total_meet):
    global best_solution
    # Prune if even picking all remaining cannot beat current best
    potential = len(path) + upper_bound_possible(current_time, remaining)
    if potential < best_solution["count"]:
        return

    improved = False
    # Try each remaining person as next
    for idx in sorted(remaining, key=lambda i: (people[i]["end"], people[i]["start"])):
        feas = feasible_next(current_loc, current_time, idx)
        if feas is None:
            continue
        start, end, t_travel, duration = feas
        # Build new state
        new_path = path + [{
            "action": "meet",
            "location": people[idx]["location"],
            "person": people[idx]["person"],
            "start_time": start,
            "end_time": end
        }]
        new_remaining = set(remaining)
        new_remaining.remove(idx)
        dfs(people[idx]["location"], end, new_remaining, new_path, total_travel + t_travel, total_meet + duration)
        improved = True

    # If no further additions or after exploring children, evaluate current path
    count = len(path)
    end_time_state = path[-1]["end_time"] if path else current_time
    if (count > best_solution["count"] or
        (count == best_solution["count"] and total_meet > best_solution["total_meet"]) or
        (count == best_solution["count"] and total_meet == best_solution["total_meet"] and end_time_state < best_solution["end_time"]) or
        (count == best_solution["count"] and total_meet == best_solution["total_meet"] and end_time_state == best_solution["end_time"] and total_travel < best_solution["total_travel"])
       ):
        best_solution = {
            "count": count,
            "total_meet": total_meet,
            "end_time": end_time_state,
            "total_travel": total_travel,
            "path": path
        }

# Start DFS
remaining_indices = set(range(len(people)))
dfs(start_location, start_time, remaining_indices, [], 0, 0)

# Prepare output
itinerary = []
for entry in best_solution["path"]:
    itinerary.append({
        "action": "meet",
        "location": entry["location"],
        "person": entry["person"],
        "start_time": fmt_time(entry["start_time"]),
        "end_time": fmt_time(entry["end_time"])
    })

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))