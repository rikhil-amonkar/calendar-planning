import json
from itertools import permutations

def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_str(m):
    h = m // 60
    min_ = m % 60
    return f"{h}:{min_:02d}"

# Travel times (in minutes), directional as provided
travel = {
    "Presidio": {
        "Pacific Heights": 11,
        "Golden Gate Park": 12,
        "Fisherman's Wharf": 19,
        "Marina District": 11,
        "Alamo Square": 19,
        "Sunset District": 15,
        "Nob Hill": 18,
        "North Beach": 18,
    },
    "Pacific Heights": {
        "Presidio": 11,
        "Golden Gate Park": 15,
        "Fisherman's Wharf": 13,
        "Marina District": 6,
        "Alamo Square": 10,
        "Sunset District": 21,
        "Nob Hill": 8,
        "North Beach": 9,
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Pacific Heights": 16,
        "Fisherman's Wharf": 24,
        "Marina District": 16,
        "Alamo Square": 9,
        "Sunset District": 10,
        "Nob Hill": 20,
        "North Beach": 23,
    },
    "Fisherman's Wharf": {
        "Presidio": 17,
        "Pacific Heights": 12,
        "Golden Gate Park": 25,
        "Marina District": 9,
        "Alamo Square": 21,
        "Sunset District": 27,
        "Nob Hill": 11,
        "North Beach": 6,
    },
    "Marina District": {
        "Presidio": 10,
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
        "Fisherman's Wharf": 10,
        "Alamo Square": 15,
        "Sunset District": 19,
        "Nob Hill": 12,
        "North Beach": 11,
    },
    "Alamo Square": {
        "Presidio": 17,
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "Fisherman's Wharf": 19,
        "Marina District": 15,
        "Sunset District": 16,
        "Nob Hill": 11,
        "North Beach": 15,
    },
    "Sunset District": {
        "Presidio": 16,
        "Pacific Heights": 21,
        "Golden Gate Park": 11,
        "Fisherman's Wharf": 29,
        "Marina District": 21,
        "Alamo Square": 17,
        "Nob Hill": 27,
        "North Beach": 28,
    },
    "Nob Hill": {
        "Presidio": 17,
        "Pacific Heights": 8,
        "Golden Gate Park": 17,
        "Fisherman's Wharf": 10,
        "Marina District": 11,
        "Alamo Square": 11,
        "Sunset District": 24,
        "North Beach": 8,
    },
    "North Beach": {
        "Presidio": 17,
        "Pacific Heights": 8,
        "Golden Gate Park": 22,
        "Fisherman's Wharf": 5,
        "Marina District": 9,
        "Alamo Square": 16,
        "Sunset District": 27,
        "Nob Hill": 7,
    },
}

# Meeting constraints
people = [
    {"name": "Kevin", "location": "Pacific Heights", "start": "7:15", "end": "8:45", "min": 90},
    {"name": "Michelle", "location": "Golden Gate Park", "start": "20:00", "end": "21:00", "min": 15},
    {"name": "Emily", "location": "Fisherman's Wharf", "start": "16:15", "end": "19:00", "min": 30},
    {"name": "Mark", "location": "Marina District", "start": "18:15", "end": "19:45", "min": 75},
    {"name": "Barbara", "location": "Alamo Square", "start": "17:00", "end": "19:00", "min": 120},
    {"name": "Laura", "location": "Sunset District", "start": "19:00", "end": "21:15", "min": 75},
    {"name": "Mary", "location": "Nob Hill", "start": "17:30", "end": "19:00", "min": 45},
    {"name": "Helen", "location": "North Beach", "start": "11:00", "end": "12:15", "min": 45},
]

# Convert times to minutes
for p in people:
    p["start_min"] = time_to_minutes(p["start"])
    p["end_min"] = time_to_minutes(p["end"])

start_location = "Presidio"
start_time = time_to_minutes("9:00")

def schedule_for_order(order):
    cur_loc = start_location
    cur_time = start_time
    itinerary = []
    total_travel = 0

    for p in order:
        loc = p["location"]
        # If travel path doesn't exist, skip (should not happen with provided data)
        if cur_loc not in travel or loc not in travel[cur_loc]:
            continue
        ttime = travel[cur_loc][loc]
        arrival = cur_time + ttime
        start = max(arrival, p["start_min"])
        end = start + p["min"]
        if end <= p["end_min"]:
            # accept meeting
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": p["name"],
                "start_time": minutes_to_str(start),
                "end_time": minutes_to_str(end),
                "_start_min": start,
                "_end_min": end,
            })
            total_travel += ttime
            cur_loc = loc
            cur_time = end
        # else skip this person
    finish_time = cur_time
    return itinerary, total_travel, finish_time

best_itinerary = []
best_score = (-1, float('-inf'), float('-inf'))  # (count, -finish_time, -total_travel)

# Explore all permutations and accept feasible meetings greedily within each order
for order in permutations(people):
    itin, ttrav, finish = schedule_for_order(order)
    count = len(itin)
    score = (count, -finish, -ttrav)
    if score > best_score:
        best_score = score
        best_itinerary = itin

# Clean itinerary output
output_itinerary = []
for item in best_itinerary:
    output_itinerary.append({
        "action": item["action"],
        "location": item["location"],
        "person": item["person"],
        "start_time": item["start_time"],
        "end_time": item["end_time"]
    })

result = {
    "itinerary": output_itinerary
}

print(json.dumps(result, indent=2))