import json

def time_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Travel times (minutes) between locations
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
    },
}

# People constraints
people = [
    # name, location, start_min, end_min, min_duration
    {"name": "Charles",  "location": "Bayview",           "start": 11*60+30, "end": 14*60+30, "duration": 45},
    {"name": "Robert",   "location": "Sunset District",   "start": 16*60+45, "end": 21*60,    "duration": 30},
    {"name": "Karen",    "location": "Richmond District", "start": 19*60+15, "end": 21*60+30, "duration": 60},
    {"name": "Rebecca",  "location": "Nob Hill",          "start": 16*60+15, "end": 20*60+30, "duration": 90},
    {"name": "Margaret", "location": "Chinatown",         "start": 14*60+15, "end": 19*60+45, "duration": 120},
    {"name": "Patricia", "location": "Haight-Ashbury",    "start": 14*60+30, "end": 20*60+30, "duration": 45},
    {"name": "Mark",     "location": "North Beach",       "start": 14*60,    "end": 18*60+30, "duration": 105},
    {"name": "Melissa",  "location": "Russian Hill",      "start": 13*60,    "end": 19*60+45, "duration": 30},
    {"name": "Laura",    "location": "Embarcadero",       "start": 7*60+45,  "end": 13*60+15, "duration": 105},
]

start_location = "Marina District"
start_time = 9 * 60  # 9:00

N = len(people)

# Precompute for memoization
from functools import lru_cache

# Map names for deterministic iteration (optional)
indices = list(range(N))

def comparator(best, candidate):
    # Each is a tuple: (count, final_end_time, total_travel, itinerary)
    # We want to maximize count; then minimize final_end_time; then minimize total_travel
    if candidate[0] != best[0]:
        return candidate[0] > best[0]
    if candidate[1] != best[1]:
        return candidate[1] < best[1]
    if candidate[2] != best[2]:
        return candidate[2] < best[2]
    return False

@lru_cache(maxsize=None)
def search(curr_loc, curr_time, met_mask):
    best = (0, curr_time, 0, [])  # count, final_end_time, total_travel, itinerary
    for i in indices:
        if (met_mask >> i) & 1:
            continue
        person = people[i]
        ttravel = travel[curr_loc][person["location"]]
        arrive = curr_time + ttravel
        start_mt = max(arrive, person["start"])
        end_mt = start_mt + person["duration"]
        if end_mt <= person["end"]:
            res = search(person["location"], end_mt, met_mask | (1 << i))
            # Build full tuple for this path
            count = res[0] + 1
            # If no further meetings, final_end is end_mt; else it's res[1]
            final_end = res[1] if res[0] > 0 else end_mt
            total_travel = res[2] + ttravel
            meeting_entry = {
                "action": "meet",
                "location": person["location"],
                "person": person["name"],
                "start_time": time_to_str(start_mt),
                "end_time": time_to_str(end_mt)
            }
            itinerary = [meeting_entry] + res[3]
            cand = (count, final_end, total_travel, itinerary)
            if comparator(best, cand):
                best = cand
    return best

best_schedule = search(start_location, start_time, 0)
itinerary = best_schedule[3]

output = {"itinerary": itinerary}
print(json.dumps(output, ensure_ascii=False))