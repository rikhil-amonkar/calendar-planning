import json

def hm(h, m):
    return h * 60 + m

def fmt(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times (in minutes) between locations
travel = {
    "Embarcadero": {
        "Richmond District": 21,
        "Union Square": 10,
        "Financial District": 5,
        "Pacific Heights": 11,
        "Nob Hill": 10,
        "Bayview": 21,
        "Embarcadero": 0,
    },
    "Richmond District": {
        "Embarcadero": 19,
        "Union Square": 21,
        "Financial District": 22,
        "Pacific Heights": 10,
        "Nob Hill": 17,
        "Bayview": 26,
        "Richmond District": 0,
    },
    "Union Square": {
        "Embarcadero": 11,
        "Richmond District": 20,
        "Financial District": 9,
        "Pacific Heights": 15,
        "Nob Hill": 9,
        "Bayview": 15,
        "Union Square": 0,
    },
    "Financial District": {
        "Embarcadero": 4,
        "Richmond District": 21,
        "Union Square": 9,
        "Pacific Heights": 13,
        "Nob Hill": 8,
        "Bayview": 19,
        "Financial District": 0,
    },
    "Pacific Heights": {
        "Embarcadero": 10,
        "Richmond District": 12,
        "Union Square": 12,
        "Financial District": 13,
        "Nob Hill": 8,
        "Bayview": 22,
        "Pacific Heights": 0,
    },
    "Nob Hill": {
        "Embarcadero": 9,
        "Richmond District": 14,
        "Union Square": 7,
        "Financial District": 9,
        "Pacific Heights": 8,
        "Bayview": 19,
        "Nob Hill": 0,
    },
    "Bayview": {
        "Embarcadero": 19,
        "Richmond District": 25,
        "Union Square": 17,
        "Financial District": 19,
        "Pacific Heights": 23,
        "Nob Hill": 20,
        "Bayview": 0,
    },
}

# People constraints
persons = [
    {
        "name": "Kenneth",
        "loc": "Richmond District",
        "start": hm(21, 15),
        "end": hm(22, 0),
        "min": 30,
    },
    {
        "name": "Lisa",
        "loc": "Union Square",
        "start": hm(9, 0),
        "end": hm(16, 30),
        "min": 45,
    },
    {
        "name": "Joshua",
        "loc": "Financial District",
        "start": hm(12, 0),
        "end": hm(15, 15),
        "min": 15,
    },
    {
        "name": "Nancy",
        "loc": "Pacific Heights",
        "start": hm(8, 0),
        "end": hm(11, 30),
        "min": 90,
    },
    {
        "name": "Andrew",
        "loc": "Nob Hill",
        "start": hm(11, 30),
        "end": hm(20, 15),
        "min": 60,
    },
    {
        "name": "John",
        "loc": "Bayview",
        "start": hm(16, 45),
        "end": hm(21, 30),
        "min": 75,
    },
]

start_location = "Embarcadero"
arrival_time = hm(9, 0)

# DFS with memoization to maximize number of meetings, then minimize finish time
from functools import lru_cache

name_order = [p["name"] for p in persons]  # to keep stable ordering if needed

@lru_cache(maxsize=None)
def dfs(loc, time, remaining_mask):
    # Returns (count_met, finish_time, itinerary_json_serializable_list)
    best_count = 0
    best_finish = time
    best_itinerary = []

    n = len(persons)
    for i in range(n):
        if not (remaining_mask & (1 << i)):
            continue
        p = persons[i]
        t_travel = travel[loc][p["loc"]]
        arrive = time + t_travel
        start = max(arrive, p["start"])
        end = start + p["min"]
        if end <= p["end"]:
            cnt, fin, itin = dfs(p["loc"], end, remaining_mask ^ (1 << i))
            cnt += 1
            # Prefer more meetings; tie-breaker: earlier finish time
            if (cnt > best_count) or (cnt == best_count and fin < best_finish):
                best_count = cnt
                best_finish = fin
                meeting = {
                    "action": "meet",
                    "location": p["loc"],
                    "person": p["name"],
                    "start_time": fmt(start),
                    "end_time": fmt(end),
                }
                best_itinerary = [meeting] + list(itin)

    return best_count, best_finish, tuple(best_itinerary)

remaining_mask = (1 << len(persons)) - 1
_, _, itinerary = dfs(start_location, arrival_time, remaining_mask)

result = {
    "itinerary": list(itinerary)
}

print(json.dumps(result, ensure_ascii=False, indent=2))