import json
from copy import deepcopy

def to_minutes(tstr):
    h, m = tstr.split(":")
    return int(h) * 60 + int(m)

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables
start_location = "Sunset District"
start_time_str = "9:00"

people = {
    "Karen": {
        "location": "Russian Hill",
        "start": "20:45",
        "end": "21:45",
        "min_duration": 60
    },
    "Jessica": {
        "location": "The Castro",
        "start": "15:45",
        "end": "19:30",
        "min_duration": 60
    },
    "Matthew": {
        "location": "Richmond District",
        "start": "7:30",
        "end": "15:15",
        "min_duration": 15
    },
    "Michelle": {
        "location": "Marina District",
        "start": "10:30",
        "end": "18:45",
        "min_duration": 75
    },
    "Carol": {
        "location": "North Beach",
        "start": "12:00",
        "end": "17:00",
        "min_duration": 90
    },
    "Stephanie": {
        "location": "Union Square",
        "start": "10:45",
        "end": "14:15",
        "min_duration": 30
    },
    "Linda": {
        "location": "Golden Gate Park",
        "start": "10:45",
        "end": "22:00",
        "min_duration": 90
    }
}

# Travel times (in minutes)
travel_times = {
    "Sunset District": {
        "Russian Hill": 24,
        "The Castro": 17,
        "Richmond District": 12,
        "Marina District": 21,
        "North Beach": 29,
        "Union Square": 30,
        "Golden Gate Park": 11
    },
    "Russian Hill": {
        "Sunset District": 23,
        "The Castro": 21,
        "Richmond District": 14,
        "Marina District": 7,
        "North Beach": 5,
        "Union Square": 11,
        "Golden Gate Park": 21
    },
    "The Castro": {
        "Sunset District": 17,
        "Russian Hill": 18,
        "Richmond District": 16,
        "Marina District": 21,
        "North Beach": 20,
        "Union Square": 19,
        "Golden Gate Park": 11
    },
    "Richmond District": {
        "Sunset District": 11,
        "Russian Hill": 13,
        "The Castro": 16,
        "Marina District": 9,
        "North Beach": 17,
        "Union Square": 21,
        "Golden Gate Park": 9
    },
    "Marina District": {
        "Sunset District": 19,
        "Russian Hill": 8,
        "The Castro": 22,
        "Richmond District": 11,
        "North Beach": 11,
        "Union Square": 16,
        "Golden Gate Park": 18
    },
    "North Beach": {
        "Sunset District": 27,
        "Russian Hill": 4,
        "The Castro": 22,
        "Richmond District": 18,
        "Marina District": 9,
        "Union Square": 7,
        "Golden Gate Park": 22
    },
    "Union Square": {
        "Sunset District": 26,
        "Russian Hill": 13,
        "The Castro": 19,
        "Richmond District": 20,
        "Marina District": 18,
        "North Beach": 10,
        "Golden Gate Park": 22
    },
    "Golden Gate Park": {
        "Sunset District": 10,
        "Russian Hill": 19,
        "The Castro": 13,
        "Richmond District": 7,
        "Marina District": 16,
        "North Beach": 24,
        "Union Square": 22
    }
}

# Ensure zero travel time to same location
for loc in list(travel_times.keys()):
    travel_times[loc][loc] = 0

# Preprocess people time windows to minutes
people_minutes = {}
for name, info in people.items():
    people_minutes[name] = {
        "location": info["location"],
        "start": to_minutes(info["start"]),
        "end": to_minutes(info["end"]),
        "min_duration": info["min_duration"]
    }

start_time = to_minutes(start_time_str)

# DFS search to maximize number of meetings.
names = list(people_minutes.keys())

best_solution = {
    "count": 0,
    "finish_time": start_time,
    "itinerary": []
}

# Simple memoization for pruning: (loc, time_rounded, met_bitmask) -> best count achieved
from functools import lru_cache

name_to_index = {n: i for i, n in enumerate(names)}

def can_meet_from(state_loc, state_time, person_name):
    p = people_minutes[person_name]
    loc = p["location"]
    travel = travel_times[state_loc][loc]
    arrival = state_time + travel
    earliest_start = max(arrival, p["start"])
    end_time = earliest_start + p["min_duration"]
    feasible = end_time <= p["end"]
    return feasible, earliest_start, end_time, loc

def dfs(current_loc, current_time, met_mask, itinerary):
    global best_solution
    met_count = bin(met_mask).count("1")

    # Update best if improved
    if met_count > best_solution["count"] or (met_count == best_solution["count"] and current_time < best_solution["finish_time"]):
        best_solution = {
            "count": met_count,
            "finish_time": current_time,
            "itinerary": deepcopy(itinerary)
        }
        # Early exit if we met everyone
        if best_solution["count"] == len(names):
            return

    # Upper bound pruning
    remaining = len(names) - met_count
    if met_count + remaining <= best_solution["count"]:
        return

    # Order candidates by earliest window end to bias toward tighter windows
    candidates = []
    for i, name in enumerate(names):
        if not (met_mask & (1 << i)):
            feasible, earliest_start, end_time, loc = can_meet_from(current_loc, current_time, name)
            if feasible:
                candidates.append((people_minutes[name]["end"], earliest_start, name, end_time, loc))
    # Sort by end time, then by earliest start
    candidates.sort()

    for _, earliest_start, name, end_time, loc in candidates:
        i = name_to_index[name]
        # Recurse with meeting scheduled at min duration
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": fmt_time(earliest_start),
            "end_time": fmt_time(end_time)
        })
        dfs(loc, end_time, met_mask | (1 << i), itinerary)
        itinerary.pop()

# Start search
dfs(start_location, start_time, 0, [])

# Build output
output = {
    "itinerary": best_solution["itinerary"]
}

print(json.dumps(output, ensure_ascii=False))