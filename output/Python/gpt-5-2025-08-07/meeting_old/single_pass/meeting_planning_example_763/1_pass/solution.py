import json
from itertools import permutations

def time_to_minutes(h, m):
    return h * 60 + m

def parse_time(s):
    # s like "15:30" or "9:00"
    parts = s.split(":")
    return time_to_minutes(int(parts[0]), int(parts[1]))

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Define travel times (in minutes) between locations
times = {
    "Chinatown": {
        "Embarcadero": 5,
        "Pacific Heights": 10,
        "Russian Hill": 7,
        "Haight-Ashbury": 19,
        "Golden Gate Park": 23,
        "Fisherman's Wharf": 8,
        "Sunset District": 29,
        "The Castro": 22,
    },
    "Embarcadero": {
        "Chinatown": 7,
        "Pacific Heights": 11,
        "Russian Hill": 8,
        "Haight-Ashbury": 21,
        "Golden Gate Park": 25,
        "Fisherman's Wharf": 6,
        "Sunset District": 30,
        "The Castro": 25,
    },
    "Pacific Heights": {
        "Chinatown": 11,
        "Embarcadero": 10,
        "Russian Hill": 7,
        "Haight-Ashbury": 11,
        "Golden Gate Park": 15,
        "Fisherman's Wharf": 13,
        "Sunset District": 21,
        "The Castro": 16,
    },
    "Russian Hill": {
        "Chinatown": 9,
        "Embarcadero": 8,
        "Pacific Heights": 7,
        "Haight-Ashbury": 17,
        "Golden Gate Park": 21,
        "Fisherman's Wharf": 7,
        "Sunset District": 23,
        "The Castro": 21,
    },
    "Haight-Ashbury": {
        "Chinatown": 19,
        "Embarcadero": 20,
        "Pacific Heights": 12,
        "Russian Hill": 17,
        "Golden Gate Park": 7,
        "Fisherman's Wharf": 23,
        "Sunset District": 15,
        "The Castro": 6,
    },
    "Golden Gate Park": {
        "Chinatown": 23,
        "Embarcadero": 25,
        "Pacific Heights": 16,
        "Russian Hill": 19,
        "Haight-Ashbury": 7,
        "Fisherman's Wharf": 24,
        "Sunset District": 10,
        "The Castro": 13,
    },
    "Fisherman's Wharf": {
        "Chinatown": 12,
        "Embarcadero": 8,
        "Pacific Heights": 12,
        "Russian Hill": 7,
        "Haight-Ashbury": 22,
        "Golden Gate Park": 25,
        "Sunset District": 27,
        "The Castro": 27,
    },
    "Sunset District": {
        "Chinatown": 30,
        "Embarcadero": 30,
        "Pacific Heights": 21,
        "Russian Hill": 24,
        "Haight-Ashbury": 15,
        "Golden Gate Park": 11,
        "Fisherman's Wharf": 29,
        "The Castro": 17,
    },
    "The Castro": {
        "Chinatown": 22,
        "Embarcadero": 22,
        "Pacific Heights": 16,
        "Russian Hill": 18,
        "Haight-Ashbury": 6,
        "Golden Gate Park": 11,
        "Fisherman's Wharf": 24,
        "Sunset District": 17,
    },
}

# Participants constraints
friends = [
    {
        "name": "Richard",
        "location": "Embarcadero",
        "start": parse_time("15:15"),
        "end": parse_time("18:45"),
        "min_duration": 90,
    },
    {
        "name": "Mark",
        "location": "Pacific Heights",
        "start": parse_time("15:00"),
        "end": parse_time("17:00"),
        "min_duration": 45,
    },
    {
        "name": "Matthew",
        "location": "Russian Hill",
        "start": parse_time("17:30"),
        "end": parse_time("21:00"),
        "min_duration": 90,
    },
    {
        "name": "Rebecca",
        "location": "Haight-Ashbury",
        "start": parse_time("14:45"),
        "end": parse_time("18:00"),
        "min_duration": 60,
    },
    {
        "name": "Melissa",
        "location": "Golden Gate Park",
        "start": parse_time("13:45"),
        "end": parse_time("17:30"),
        "min_duration": 90,
    },
    {
        "name": "Margaret",
        "location": "Fisherman's Wharf",
        "start": parse_time("14:45"),
        "end": parse_time("20:15"),
        "min_duration": 15,
    },
    {
        "name": "Emily",
        "location": "Sunset District",
        "start": parse_time("15:45"),
        "end": parse_time("17:00"),
        "min_duration": 45,
    },
    {
        "name": "George",
        "location": "The Castro",
        "start": parse_time("14:00"),
        "end": parse_time("16:15"),
        "min_duration": 75,
    },
]

start_location = "Chinatown"
start_time = parse_time("9:00")

# DFS search to maximize number of meetings (primary), then earliest finish time (secondary), then minimal total travel time (tertiary)
best_solution = {
    "count": 0,
    "finish_time": float('inf'),
    "total_travel": float('inf'),
    "itinerary": [],
}

def update_best(itinerary, finish_time, total_travel):
    global best_solution
    count = len(itinerary)
    better = False
    if count > best_solution["count"]:
        better = True
    elif count == best_solution["count"]:
        if finish_time < best_solution["finish_time"]:
            better = True
        elif finish_time == best_solution["finish_time"]:
            if total_travel < best_solution["total_travel"]:
                better = True
    if better:
        best_solution = {
            "count": count,
            "finish_time": finish_time,
            "total_travel": total_travel,
            "itinerary": itinerary[:],
        }

def dfs(curr_loc, curr_time, remaining, itinerary, total_travel):
    # Update best at current node (option to stop here)
    last_time = curr_time if not itinerary else itinerary[-1]["end_minutes"]
    update_best(itinerary, last_time, total_travel)

    for idx, friend in enumerate(remaining):
        # travel time to friend's location
        tt = times[curr_loc][friend["location"]]
        arrival = curr_time + tt
        start_meet = max(arrival, friend["start"])
        end_meet = start_meet + friend["min_duration"]
        if end_meet > friend["end"]:
            continue  # infeasible
        # Recurse
        new_entry = {
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_str(start_meet),
            "end_time": minutes_to_str(end_meet),
            "start_minutes": start_meet,
            "end_minutes": end_meet,
        }
        itinerary.append(new_entry)
        next_remaining = remaining[:idx] + remaining[idx+1:]
        dfs(friend["location"], end_meet, next_remaining, itinerary, total_travel + tt)
        itinerary.pop()

# Start search
dfs(start_location, start_time, friends, [], 0)

# Prepare final JSON output (strip helper minute fields)
output_itinerary = []
for e in best_solution["itinerary"]:
    output_itinerary.append({
        "action": "meet",
        "location": e["location"],
        "person": e["person"],
        "start_time": e["start_time"],
        "end_time": e["end_time"],
    })

result = {"itinerary": output_itinerary}
print(json.dumps(result, ensure_ascii=False))