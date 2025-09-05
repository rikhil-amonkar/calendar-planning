import json
from copy import deepcopy

# Helper functions for time conversion
def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_str_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Travel times in minutes between locations
locations = [
    "Marina District", "Bayview", "Sunset District", "Richmond District",
    "Nob Hill", "Chinatown", "Haight-Ashbury", "North Beach", "Russian Hill", "Embarcadero"
]

travel = {
    "Marina District": {
        "Bayview": 27, "Sunset District": 19, "Richmond District": 11, "Nob Hill": 12,
        "Chinatown": 15, "Haight-Ashbury": 16, "North Beach": 11, "Russian Hill": 8, "Embarcadero": 14
    },
    "Bayview": {
        "Marina District": 27, "Sunset District": 23, "Richmond District": 25, "Nob Hill": 20,
        "Chinatown": 19, "Haight-Ashbury": 19, "North Beach": 22, "Russian Hill": 23, "Embarcadero": 19
    },
    "Sunset District": {
        "Marina District": 21, "Bayview": 22, "Richmond District": 12, "Nob Hill": 27,
        "Chinatown": 30, "Haight-Ashbury": 15, "North Beach": 28, "Russian Hill": 24, "Embarcadero": 30
    },
    "Richmond District": {
        "Marina District": 9, "Bayview": 27, "Sunset District": 11, "Nob Hill": 17,
        "Chinatown": 20, "Haight-Ashbury": 10, "North Beach": 17, "Russian Hill": 13, "Embarcadero": 19
    },
    "Nob Hill": {
        "Marina District": 11, "Bayview": 19, "Sunset District": 24, "Richmond District": 14,
        "Chinatown": 6, "Haight-Ashbury": 13, "North Beach": 8, "Russian Hill": 5, "Embarcadero": 9
    },
    "Chinatown": {
        "Marina District": 12, "Bayview": 20, "Sunset District": 29, "Richmond District": 20,
        "Nob Hill": 9, "Haight-Ashbury": 19, "North Beach": 3, "Russian Hill": 7, "Embarcadero": 5
    },
    "Haight-Ashbury": {
        "Marina District": 17, "Bayview": 18, "Sunset District": 15, "Richmond District": 10,
        "Nob Hill": 15, "Chinatown": 19, "North Beach": 19, "Russian Hill": 17, "Embarcadero": 20
    },
    "North Beach": {
        "Marina District": 9, "Bayview": 25, "Sunset District": 27, "Richmond District": 18,
        "Nob Hill": 7, "Chinatown": 6, "Haight-Ashbury": 18, "Russian Hill": 4, "Embarcadero": 6
    },
    "Russian Hill": {
        "Marina District": 7, "Bayview": 23, "Sunset District": 23, "Richmond District": 14,
        "Nob Hill": 5, "Chinatown": 9, "Haight-Ashbury": 17, "North Beach": 5, "Embarcadero": 8
    },
    "Embarcadero": {
        "Marina District": 12, "Bayview": 21, "Sunset District": 30, "Richmond District": 21,
        "Nob Hill": 10, "Chinatown": 7, "Haight-Ashbury": 21, "North Beach": 5, "Russian Hill": 8
    }
}

# Add zero travel within the same location
for loc in locations:
    travel.setdefault(loc, {})
    travel[loc][loc] = 0

# Meeting constraints
people = [
    {"name": "Charles", "location": "Bayview", "start": to_minutes("11:30"), "end": to_minutes("14:30"), "min_duration": 45},
    {"name": "Robert", "location": "Sunset District", "start": to_minutes("16:45"), "end": to_minutes("21:00"), "min_duration": 30},
    {"name": "Karen", "location": "Richmond District", "start": to_minutes("19:15"), "end": to_minutes("21:30"), "min_duration": 60},
    {"name": "Rebecca", "location": "Nob Hill", "start": to_minutes("16:15"), "end": to_minutes("20:30"), "min_duration": 90},
    {"name": "Margaret", "location": "Chinatown", "start": to_minutes("14:15"), "end": to_minutes("19:45"), "min_duration": 120},
    {"name": "Patricia", "location": "Haight-Ashbury", "start": to_minutes("14:30"), "end": to_minutes("20:30"), "min_duration": 45},
    {"name": "Mark", "location": "North Beach", "start": to_minutes("14:00"), "end": to_minutes("18:30"), "min_duration": 105},
    {"name": "Melissa", "location": "Russian Hill", "start": to_minutes("13:00"), "end": to_minutes("19:45"), "min_duration": 30},
    {"name": "Laura", "location": "Embarcadero", "start": to_minutes("7:45"), "end": to_minutes("13:15"), "min_duration": 105},
]

start_location = "Marina District"
start_time = to_minutes("9:00")

# Precompute a helpful order key: earliest feasible start and tightness (end - (start + min_duration))
def heuristic_key(person):
    return (person["end"], person["start"], person["min_duration"])

# DFS search for optimal schedule
best = {
    "count": 0,
    "penalty": float("inf"),
    "end_time": float("inf"),
    "itinerary": []
}

def try_schedule(current_loc, current_time, remaining, itinerary, travel_sum, wait_sum):
    global best

    # Evaluate current partial solution
    current_count = len(itinerary)
    penalty = travel_sum + wait_sum
    if (current_count > best["count"] or
        (current_count == best["count"] and (penalty < best["penalty"] or
         (penalty == best["penalty"] and current_time < best["end_time"])))):
        best = {
            "count": current_count,
            "penalty": penalty,
            "end_time": current_time,
            "itinerary": deepcopy(itinerary)
        }

    if not remaining:
        return

    # Upper bound pruning: even if we meet everyone remaining, can we beat best?
    if current_count + len(remaining) < best["count"]:
        return

    # Sort candidates to try promising ones first
    candidates = sorted(remaining, key=heuristic_key)

    for i, p in enumerate(candidates):
        # Travel to person's location
        ttime = travel[current_loc][p["location"]]
        arrival = current_time + ttime
        start_meet = max(arrival, p["start"])
        end_meet = start_meet + p["min_duration"]

        # Feasibility check
        if end_meet > p["end"]:
            continue

        # Calculate wait
        wait = max(0, p["start"] - arrival)

        # New state
        next_itin = itinerary + [{
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": to_str_time(start_meet),
            "end_time": to_str_time(end_meet)
        }]

        next_remaining = [x for j, x in enumerate(candidates) if j != i]
        # Recurse
        try_schedule(p["location"], end_meet, next_remaining, next_itin, travel_sum + ttime, wait_sum + wait)

# Begin search
try_schedule(start_location, start_time, people, [], 0, 0)

# Output result as JSON
output = {
    "itinerary": best["itinerary"]
}

print(json.dumps(output, ensure_ascii=False))