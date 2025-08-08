import json

# Helper functions
def parse_time(s):
    h, m = map(int, s.split(":"))
    return h * 60 + m

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times (in minutes) between locations
travel = {
    "Chinatown": {
        "Mission District": 18,
        "Alamo Square": 17,
        "Pacific Heights": 10,
        "Union Square": 7,
        "Golden Gate Park": 23,
        "Sunset District": 29,
        "Presidio": 19,
    },
    "Mission District": {
        "Chinatown": 16,
        "Alamo Square": 11,
        "Pacific Heights": 16,
        "Union Square": 15,
        "Golden Gate Park": 17,
        "Sunset District": 24,
        "Presidio": 25,
    },
    "Alamo Square": {
        "Chinatown": 16,
        "Mission District": 10,
        "Pacific Heights": 10,
        "Union Square": 14,
        "Golden Gate Park": 9,
        "Sunset District": 16,
        "Presidio": 18,
    },
    "Pacific Heights": {
        "Chinatown": 11,
        "Mission District": 15,
        "Alamo Square": 10,
        "Union Square": 12,
        "Golden Gate Park": 15,
        "Sunset District": 21,
        "Presidio": 11,
    },
    "Union Square": {
        "Chinatown": 7,
        "Mission District": 14,
        "Alamo Square": 15,
        "Pacific Heights": 15,
        "Golden Gate Park": 22,
        "Sunset District": 26,
        "Presidio": 24,
    },
    "Golden Gate Park": {
        "Chinatown": 23,
        "Mission District": 17,
        "Alamo Square": 10,
        "Pacific Heights": 16,
        "Union Square": 22,
        "Sunset District": 10,
        "Presidio": 11,
    },
    "Sunset District": {
        "Chinatown": 30,
        "Mission District": 24,
        "Alamo Square": 17,
        "Pacific Heights": 21,
        "Union Square": 30,
        "Golden Gate Park": 11,
        "Presidio": 16,
    },
    "Presidio": {
        "Chinatown": 21,
        "Mission District": 26,
        "Alamo Square": 18,
        "Pacific Heights": 11,
        "Union Square": 22,
        "Golden Gate Park": 12,
        "Sunset District": 15,
    },
}

# Participants and constraints
people = {
    "David": {
        "location": "Mission District",
        "start": parse_time("8:00"),
        "end": parse_time("19:45"),
        "min_duration": 45,
    },
    "Kenneth": {
        "location": "Alamo Square",
        "start": parse_time("14:00"),
        "end": parse_time("19:45"),
        "min_duration": 120,
    },
    "John": {
        "location": "Pacific Heights",
        "start": parse_time("17:00"),
        "end": parse_time("20:00"),
        "min_duration": 15,
    },
    "Charles": {
        "location": "Union Square",
        "start": parse_time("21:45"),
        "end": parse_time("22:45"),
        "min_duration": 60,
    },
    "Deborah": {
        "location": "Golden Gate Park",
        "start": parse_time("7:00"),
        "end": parse_time("18:15"),
        "min_duration": 90,
    },
    "Karen": {
        "location": "Sunset District",
        "start": parse_time("17:45"),
        "end": parse_time("21:15"),
        "min_duration": 15,
    },
    "Carol": {
        "location": "Presidio",
        "start": parse_time("8:15"),
        "end": parse_time("9:15"),
        "min_duration": 30,
    },
}

start_location = "Chinatown"
start_time = parse_time("9:00")

# DFS with memoization to find optimal schedule
from functools import lru_cache

names_sorted = sorted(people.keys())

@lru_cache(maxsize=None)
def dfs(curr_loc, curr_time, remaining_frozenset):
    remaining = list(remaining_frozenset)
    best = {
        "count": 0,
        "end_time": curr_time,
        "wait": 0,
        "itinerary": (),
    }
    # Iterate deterministically over remaining names
    for name in sorted(remaining):
        p = people[name]
        to_loc = p["location"]
        # If no travel path (shouldn't happen), skip
        if curr_loc not in travel or to_loc not in travel[curr_loc]:
            continue
        travel_time = travel[curr_loc][to_loc]
        arrival = curr_time + travel_time
        start_meet = max(arrival, p["start"])
        end_meet = start_meet + p["min_duration"]
        if end_meet <= p["end"]:
            waiting = max(0, p["start"] - arrival)
            next_remaining = frozenset([n for n in remaining if n != name])
            res = dfs(to_loc, end_meet, next_remaining)
            new_count = 1 + res["count"]
            new_end_time = res["end_time"]
            new_wait = waiting + res["wait"]
            new_itinerary = (
                ("meet", to_loc, name, start_meet, end_meet),
            ) + res["itinerary"]
            # Choose better result: more meetings, then earlier end, then less waiting, then lexicographic itinerary for determinism
            def better(a, b):
                if a["count"] != b["count"]:
                    return a["count"] > b["count"]
                if a["end_time"] != b["end_time"]:
                    return a["end_time"] < b["end_time"]
                if a["wait"] != b["wait"]:
                    return a["wait"] < b["wait"]
                return a["itinerary"] < b["itinerary"]
            candidate = {
                "count": new_count,
                "end_time": new_end_time,
                "wait": new_wait,
                "itinerary": new_itinerary,
            }
            if better(candidate, best):
                best = candidate
    return best

result = dfs(start_location, start_time, frozenset(people.keys()))

# Convert itinerary to required JSON format
output = {"itinerary": []}
for action, location, person, start_m, end_m in result["itinerary"]:
    output["itinerary"].append({
        "action": "meet",
        "location": location,
        "person": person,
        "start_time": minutes_to_str(start_m),
        "end_time": minutes_to_str(end_m),
    })

print(json.dumps(output))