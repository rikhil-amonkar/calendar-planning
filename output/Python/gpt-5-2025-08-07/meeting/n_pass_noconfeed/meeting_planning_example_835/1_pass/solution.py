import json
from copy import deepcopy

def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times in minutes (directed)
times = {
    "Pacific Heights": {
        "Golden Gate Park": 15,
        "The Castro": 16,
        "Bayview": 22,
        "Marina District": 6,
        "Union Square": 12,
        "Sunset District": 21,
        "Alamo Square": 10,
        "Financial District": 13,
        "Mission District": 15,
    },
    "Golden Gate Park": {
        "Pacific Heights": 16,
        "The Castro": 13,
        "Bayview": 23,
        "Marina District": 16,
        "Union Square": 22,
        "Sunset District": 10,
        "Alamo Square": 9,
        "Financial District": 26,
        "Mission District": 17,
    },
    "The Castro": {
        "Pacific Heights": 16,
        "Golden Gate Park": 11,
        "Bayview": 19,
        "Marina District": 21,
        "Union Square": 19,
        "Sunset District": 17,
        "Alamo Square": 8,
        "Financial District": 21,
        "Mission District": 7,
    },
    "Bayview": {
        "Pacific Heights": 23,
        "Golden Gate Park": 22,
        "The Castro": 19,
        "Marina District": 27,
        "Union Square": 18,
        "Sunset District": 23,
        "Alamo Square": 16,
        "Financial District": 19,
        "Mission District": 13,
    },
    "Marina District": {
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
        "The Castro": 22,
        "Bayview": 27,
        "Union Square": 16,
        "Sunset District": 19,
        "Alamo Square": 15,
        "Financial District": 17,
        "Mission District": 20,
    },
    "Union Square": {
        "Pacific Heights": 15,
        "Golden Gate Park": 22,
        "The Castro": 17,
        "Bayview": 15,
        "Marina District": 18,
        "Sunset District": 27,
        "Alamo Square": 15,
        "Financial District": 9,
        "Mission District": 14,
    },
    "Sunset District": {
        "Pacific Heights": 21,
        "Golden Gate Park": 11,
        "The Castro": 17,
        "Bayview": 22,
        "Marina District": 21,
        "Union Square": 30,
        "Alamo Square": 17,
        "Financial District": 30,
        "Mission District": 25,
    },
    "Alamo Square": {
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "The Castro": 8,
        "Bayview": 16,
        "Marina District": 15,
        "Union Square": 14,
        "Sunset District": 16,
        "Financial District": 17,
        "Mission District": 10,
    },
    "Financial District": {
        "Pacific Heights": 13,
        "Golden Gate Park": 23,
        "The Castro": 20,
        "Bayview": 19,
        "Marina District": 15,
        "Union Square": 9,
        "Sunset District": 30,
        "Alamo Square": 17,
        "Mission District": 17,
    },
    "Mission District": {
        "Pacific Heights": 16,
        "Golden Gate Park": 17,
        "The Castro": 7,
        "Bayview": 14,
        "Marina District": 19,
        "Union Square": 15,
        "Sunset District": 24,
        "Alamo Square": 11,
        "Financial District": 15,
    },
}

# Participants and constraints
participants = [
    {
        "name": "Helen",
        "location": "Golden Gate Park",
        "start": time_to_minutes("9:30"),
        "end": time_to_minutes("12:15"),
        "min_duration": 45,
    },
    {
        "name": "Steven",
        "location": "The Castro",
        "start": time_to_minutes("20:15"),
        "end": time_to_minutes("22:00"),
        "min_duration": 105,
    },
    {
        "name": "Deborah",
        "location": "Bayview",
        "start": time_to_minutes("8:30"),
        "end": time_to_minutes("12:00"),
        "min_duration": 30,
    },
    {
        "name": "Matthew",
        "location": "Marina District",
        "start": time_to_minutes("9:15"),
        "end": time_to_minutes("14:15"),
        "min_duration": 45,
    },
    {
        "name": "Joseph",
        "location": "Union Square",
        "start": time_to_minutes("14:15"),
        "end": time_to_minutes("18:45"),
        "min_duration": 120,
    },
    {
        "name": "Ronald",
        "location": "Sunset District",
        "start": time_to_minutes("16:00"),
        "end": time_to_minutes("20:45"),
        "min_duration": 60,
    },
    {
        "name": "Robert",
        "location": "Alamo Square",
        "start": time_to_minutes("18:30"),
        "end": time_to_minutes("21:15"),
        "min_duration": 120,
    },
    {
        "name": "Rebecca",
        "location": "Financial District",
        "start": time_to_minutes("14:45"),
        "end": time_to_minutes("16:15"),
        "min_duration": 30,
    },
    {
        "name": "Elizabeth",
        "location": "Mission District",
        "start": time_to_minutes("18:30"),
        "end": time_to_minutes("21:00"),
        "min_duration": 120,
    },
]

# Precompute latest feasible start times to speed feasibility checks
for p in participants:
    p["latest_start"] = p["end"] - p["min_duration"]

start_location = "Pacific Heights"
start_time = time_to_minutes("9:00")

# Sort participants to try earlier deadline tasks first (heuristic)
order = sorted(range(len(participants)), key=lambda i: participants[i]["end"])

best_solution = {
    "itinerary": [],
    "count": 0,
    "finish_time": start_time,
}

# Simple memoization with rounding time to the minute; state space is small
from functools import lru_cache

# We'll map locations to indices for memoization
loc_index = {loc: idx for idx, loc in enumerate(times.keys())}
loc_names = list(times.keys())

@lru_cache(maxsize=None)
def dfs(current_loc_idx, current_time, remaining_mask):
    # Returns tuple: (count, finish_time, itinerary)
    # itinerary is a list of entries (person_index, start_time, end_time)
    best = (0, current_time, [])
    remaining_indices = [i for i in order if (remaining_mask >> i) & 1]

    # Upper bound pruning: if even taking all remaining we can't beat current best along this path,
    # handled implicitly by recursion order in memoization.
    for i in remaining_indices:
        p = participants[i]
        # Travel time
        curr_loc = loc_names[current_loc_idx]
        travel_time = times[curr_loc][p["location"]]
        arrival = current_time + travel_time

        # Feasibility check using latest_start
        if arrival > p["latest_start"]:
            continue  # cannot fit minimum duration

        start_mt = max(arrival, p["start"])
        end_mt = start_mt + p["min_duration"]
        if end_mt > p["end"]:
            continue

        # Recurse
        new_mask = remaining_mask & ~(1 << i)
        next_loc_idx = loc_index[p["location"]]
        sub_count, sub_finish, sub_itin = dfs(next_loc_idx, end_mt, new_mask)

        # Include this meeting
        total_count = 1 + sub_count
        total_finish = sub_finish
        itinerary = [(i, start_mt, end_mt)] + sub_itin

        # Compare with current best: maximize count, then minimize finish time
        if total_count > best[0] or (total_count == best[0] and total_finish < best[1]):
            best = (total_count, total_finish, itinerary)

    return best

# Build the initial remaining mask (all participants available)
remaining_mask = 0
for i in range(len(participants)):
    remaining_mask |= (1 << i)

count, finish, plan = dfs(loc_index[start_location], start_time, remaining_mask)

# Convert plan to output format (reverse since we constructed from current to future)
plan = list(reversed(plan))
itinerary_output = []
current_loc = start_location
current_time_ptr = start_time

for i, start_mt, end_mt in plan:
    p = participants[i]
    itinerary_output.append({
        "action": "meet",
        "location": p["location"],
        "person": p["name"],
        "start_time": minutes_to_time(start_mt),
        "end_time": minutes_to_time(end_mt),
    })
    current_loc = p["location"]
    current_time_ptr = end_mt

output = {
    "itinerary": itinerary_output
}

print(json.dumps(output))