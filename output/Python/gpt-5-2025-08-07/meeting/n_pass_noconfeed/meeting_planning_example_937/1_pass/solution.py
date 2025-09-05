import json
from copy import deepcopy

# SOLUTION:

def time_to_minutes(t):
    # t like "9:00", "13:30" already 24h in input variables; helper if needed
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Travel times in minutes (directed)
travel = {
    "Russian Hill": {
        "Sunset District": 23,
        "Union Square": 10,
        "Nob Hill": 5,
        "Marina District": 7,
        "Richmond District": 14,
        "Financial District": 11,
        "Embarcadero": 8,
        "The Castro": 21,
        "Alamo Square": 15,
        "Presidio": 14,
    },
    "Sunset District": {
        "Russian Hill": 24,
        "Union Square": 30,
        "Nob Hill": 27,
        "Marina District": 21,
        "Richmond District": 12,
        "Financial District": 30,
        "Embarcadero": 30,
        "The Castro": 17,
        "Alamo Square": 17,
        "Presidio": 16,
    },
    "Union Square": {
        "Russian Hill": 13,
        "Sunset District": 27,
        "Nob Hill": 9,
        "Marina District": 18,
        "Richmond District": 20,
        "Financial District": 9,
        "Embarcadero": 11,
        "The Castro": 17,
        "Alamo Square": 15,
        "Presidio": 24,
    },
    "Nob Hill": {
        "Russian Hill": 5,
        "Sunset District": 24,
        "Union Square": 7,
        "Marina District": 11,
        "Richmond District": 14,
        "Financial District": 9,
        "Embarcadero": 9,
        "The Castro": 17,
        "Alamo Square": 11,
        "Presidio": 17,
    },
    "Marina District": {
        "Russian Hill": 8,
        "Sunset District": 19,
        "Union Square": 16,
        "Nob Hill": 12,
        "Richmond District": 11,
        "Financial District": 17,
        "Embarcadero": 14,
        "The Castro": 22,
        "Alamo Square": 15,
        "Presidio": 10,
    },
    "Richmond District": {
        "Russian Hill": 13,
        "Sunset District": 11,
        "Union Square": 21,
        "Nob Hill": 17,
        "Marina District": 9,
        "Financial District": 22,
        "Embarcadero": 19,
        "The Castro": 16,
        "Alamo Square": 13,
        "Presidio": 7,
    },
    "Financial District": {
        "Russian Hill": 11,
        "Sunset District": 30,
        "Union Square": 9,
        "Nob Hill": 8,
        "Marina District": 15,
        "Richmond District": 21,
        "Embarcadero": 4,
        "The Castro": 20,
        "Alamo Square": 17,
        "Presidio": 22,
    },
    "Embarcadero": {
        "Russian Hill": 8,
        "Sunset District": 30,
        "Union Square": 10,
        "Nob Hill": 10,
        "Marina District": 12,
        "Richmond District": 21,
        "Financial District": 5,
        "The Castro": 25,
        "Alamo Square": 19,
        "Presidio": 20,
    },
    "The Castro": {
        "Russian Hill": 18,
        "Sunset District": 17,
        "Union Square": 19,
        "Nob Hill": 16,
        "Marina District": 21,
        "Richmond District": 16,
        "Financial District": 21,
        "Embarcadero": 22,
        "Alamo Square": 8,
        "Presidio": 20,
    },
    "Alamo Square": {
        "Russian Hill": 13,
        "Sunset District": 16,
        "Union Square": 14,
        "Nob Hill": 11,
        "Marina District": 15,
        "Richmond District": 11,
        "Financial District": 17,
        "Embarcadero": 16,
        "The Castro": 8,
        "Presidio": 17,
    },
    "Presidio": {
        "Russian Hill": 14,
        "Sunset District": 15,
        "Union Square": 22,
        "Nob Hill": 18,
        "Marina District": 11,
        "Richmond District": 7,
        "Financial District": 23,
        "Embarcadero": 20,
        "The Castro": 21,
        "Alamo Square": 19,
    },
}

# Meeting constraints
# All times in minutes from midnight using 24-hour clock
def hm(h, m):
    return h * 60 + m

friends = [
    {"person": "David", "location": "Sunset District", "start": hm(9, 15), "end": hm(22, 0), "min": 15},
    {"person": "Kenneth", "location": "Union Square", "start": hm(21, 15), "end": hm(21, 45), "min": 15},
    {"person": "Patricia", "location": "Nob Hill", "start": hm(15, 0), "end": hm(19, 15), "min": 120},
    {"person": "Mary", "location": "Marina District", "start": hm(14, 45), "end": hm(16, 45), "min": 45},
    {"person": "Charles", "location": "Richmond District", "start": hm(17, 15), "end": hm(21, 0), "min": 15},
    {"person": "Joshua", "location": "Financial District", "start": hm(14, 30), "end": hm(17, 15), "min": 90},
    {"person": "Ronald", "location": "Embarcadero", "start": hm(18, 15), "end": hm(20, 45), "min": 30},
    {"person": "George", "location": "The Castro", "start": hm(14, 15), "end": hm(19, 0), "min": 105},
    {"person": "Kimberly", "location": "Alamo Square", "start": hm(9, 0), "end": hm(14, 30), "min": 105},
    {"person": "William", "location": "Presidio", "start": hm(7, 0), "end": hm(12, 45), "min": 60},
]

start_location = "Russian Hill"
start_time = hm(9, 0)

# Precompute a map by person name for convenience
friend_map = {f["person"]: f for f in friends}
people = [f["person"] for f in friends]

# DFS with pruning to maximize number of friends met; tie-breaker: earliest finish time
best_solution = {
    "count": 0,
    "end_time": float("inf"),
    "itinerary": [],
}

def dfs(current_loc, current_time, remaining_names, itinerary, total_wait):
    global best_solution

    # Update best at leaf or intermediate
    if len(itinerary) > best_solution["count"] or (
        len(itinerary) == best_solution["count"] and (itinerary[-1]["end"] if itinerary else current_time) < best_solution["end_time"]
    ):
        best_solution = {
            "count": len(itinerary),
            "end_time": itinerary[-1]["end"] if itinerary else current_time,
            "itinerary": deepcopy(itinerary),
        }

    # Upper bound pruning
    if len(itinerary) + len(remaining_names) <= best_solution["count"]:
        return

    # Order candidates by earliest latest feasible start (end - min)
    ordered = sorted(
        remaining_names,
        key=lambda name: (friend_map[name]["end"] - friend_map[name]["min"])
    )

    for name in ordered:
        f = friend_map[name]
        # Travel time
        if current_loc not in travel or f["location"] not in travel[current_loc]:
            continue  # safety
        t_travel = travel[current_loc][f["location"]]
        arrival = current_time + t_travel
        latest_start = f["end"] - f["min"]

        if arrival > latest_start:
            continue  # can't fit even if we start immediately upon arrival

        start_meet = max(arrival, f["start"])
        end_meet = start_meet + f["min"]
        if end_meet > f["end"]:
            continue  # not enough time

        wait_here = max(0, f["start"] - arrival)

        itinerary.append({
            "action": "meet",
            "location": f["location"],
            "person": f["person"],
            "start": start_meet,
            "end": end_meet,
        })
        new_remaining = [n for n in remaining_names if n != name]
        dfs(f["location"], end_meet, new_remaining, itinerary, total_wait + wait_here)
        itinerary.pop()

# Start search
dfs(start_location, start_time, people, [], 0)

# Build JSON output
output = {
    "itinerary": [
        {
            "action": item["action"],
            "location": item["location"],
            "person": item["person"],
            "start_time": minutes_to_time(item["start"]),
            "end_time": minutes_to_time(item["end"]),
        }
        for item in best_solution["itinerary"]
    ]
}

print(json.dumps(output, ensure_ascii=False))