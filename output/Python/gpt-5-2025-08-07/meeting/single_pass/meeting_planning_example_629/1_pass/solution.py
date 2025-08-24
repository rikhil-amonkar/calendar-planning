import json
from itertools import permutations

def to_minutes(h, m):
    return h*60 + m

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Input variables (constraints)
start_location = "Russian Hill"
start_time = to_minutes(9, 0)

people = [
    {"name": "Matthew", "location": "Presidio", "start": to_minutes(11, 0), "end": to_minutes(21, 0), "min_dur": 90},
    {"name": "Margaret", "location": "Chinatown", "start": to_minutes(9, 15), "end": to_minutes(18, 45), "min_dur": 90},
    {"name": "Nancy", "location": "Pacific Heights", "start": to_minutes(14, 15), "end": to_minutes(17, 0), "min_dur": 15},
    {"name": "Helen", "location": "Richmond District", "start": to_minutes(19, 45), "end": to_minutes(22, 0), "min_dur": 60},
    {"name": "Rebecca", "location": "Fisherman's Wharf", "start": to_minutes(21, 15), "end": to_minutes(22, 15), "min_dur": 60},
    {"name": "Kimberly", "location": "Golden Gate Park", "start": to_minutes(13, 0), "end": to_minutes(16, 30), "min_dur": 120},
    {"name": "Kenneth", "location": "Bayview", "start": to_minutes(14, 30), "end": to_minutes(18, 0), "min_dur": 60},
]

# Travel time matrix (minutes)
locs = [
    "Russian Hill", "Presidio", "Chinatown", "Pacific Heights",
    "Richmond District", "Fisherman's Wharf", "Golden Gate Park", "Bayview"
]

travel = {a: {} for a in locs}
# Fill zero for same-location travel
for a in locs:
    travel[a][a] = 0

# Given travel times
travel["Russian Hill"]["Presidio"] = 14
travel["Russian Hill"]["Chinatown"] = 9
travel["Russian Hill"]["Pacific Heights"] = 7
travel["Russian Hill"]["Richmond District"] = 14
travel["Russian Hill"]["Fisherman's Wharf"] = 7
travel["Russian Hill"]["Golden Gate Park"] = 21
travel["Russian Hill"]["Bayview"] = 23

travel["Presidio"]["Russian Hill"] = 14
travel["Presidio"]["Chinatown"] = 21
travel["Presidio"]["Pacific Heights"] = 11
travel["Presidio"]["Richmond District"] = 7
travel["Presidio"]["Fisherman's Wharf"] = 19
travel["Presidio"]["Golden Gate Park"] = 12
travel["Presidio"]["Bayview"] = 31

travel["Chinatown"]["Russian Hill"] = 7
travel["Chinatown"]["Presidio"] = 19
travel["Chinatown"]["Pacific Heights"] = 10
travel["Chinatown"]["Richmond District"] = 20
travel["Chinatown"]["Fisherman's Wharf"] = 8
travel["Chinatown"]["Golden Gate Park"] = 23
travel["Chinatown"]["Bayview"] = 22

travel["Pacific Heights"]["Russian Hill"] = 7
travel["Pacific Heights"]["Presidio"] = 11
travel["Pacific Heights"]["Chinatown"] = 11
travel["Pacific Heights"]["Richmond District"] = 12
travel["Pacific Heights"]["Fisherman's Wharf"] = 13
travel["Pacific Heights"]["Golden Gate Park"] = 15
travel["Pacific Heights"]["Bayview"] = 22

travel["Richmond District"]["Russian Hill"] = 13
travel["Richmond District"]["Presidio"] = 7
travel["Richmond District"]["Chinatown"] = 20
travel["Richmond District"]["Pacific Heights"] = 10
travel["Richmond District"]["Fisherman's Wharf"] = 18
travel["Richmond District"]["Golden Gate Park"] = 9
travel["Richmond District"]["Bayview"] = 26

travel["Fisherman's Wharf"]["Russian Hill"] = 7
travel["Fisherman's Wharf"]["Presidio"] = 17
travel["Fisherman's Wharf"]["Chinatown"] = 12
travel["Fisherman's Wharf"]["Pacific Heights"] = 12
travel["Fisherman's Wharf"]["Richmond District"] = 18
travel["Fisherman's Wharf"]["Golden Gate Park"] = 25
travel["Fisherman's Wharf"]["Bayview"] = 26

travel["Golden Gate Park"]["Russian Hill"] = 19
travel["Golden Gate Park"]["Presidio"] = 11
travel["Golden Gate Park"]["Chinatown"] = 23
travel["Golden Gate Park"]["Pacific Heights"] = 16
travel["Golden Gate Park"]["Richmond District"] = 7
travel["Golden Gate Park"]["Fisherman's Wharf"] = 24
travel["Golden Gate Park"]["Bayview"] = 23

travel["Bayview"]["Russian Hill"] = 23
travel["Bayview"]["Presidio"] = 31
travel["Bayview"]["Chinatown"] = 18
travel["Bayview"]["Pacific Heights"] = 23
travel["Bayview"]["Richmond District"] = 25
travel["Bayview"]["Fisherman's Wharf"] = 25
travel["Bayview"]["Golden Gate Park"] = 22

def earliest_feasible(cur_loc, cur_time, person):
    t_travel = travel[cur_loc][person["location"]]
    arrival = cur_time + t_travel
    start = max(arrival, person["start"])
    end = start + person["min_dur"]
    if end <= person["end"]:
        return start, end, t_travel
    return None

def better_solution(a, b):
    # Compare two solutions tuples: (count, end_time, total_travel, itinerary)
    if a is None:
        return False
    if b is None:
        return True
    if a[0] != b[0]:
        return a[0] > b[0]
    if a[1] != b[1]:
        return a[1] < b[1]  # earlier finish is better
    if a[2] != b[2]:
        return a[2] < b[2]  # less travel is better
    return False

from functools import lru_cache

# Use DFS over subsets; memoization on (cur_loc, cur_time, remaining_mask)
name_to_index = {p["name"]: i for i, p in enumerate(people)}

@lru_cache(maxsize=None)
def dfs(cur_loc, cur_time, remaining_mask):
    best = (0, cur_time, 0, [])  # base: no more meetings
    # Try each remaining person
    for i, person in enumerate(people):
        if not (remaining_mask & (1 << i)):
            continue
        feas = earliest_feasible(cur_loc, cur_time, person)
        if feas is None:
            continue
        start, end, t_travel = feas
        next_mask = remaining_mask ^ (1 << i)
        sub = dfs(person["location"], end, next_mask)
        # Combine
        count = 1 + sub[0]
        end_time = sub[1]
        total_travel = t_travel + sub[2]
        itinerary = [{
            "action": "meet",
            "location": person["location"],
            "person": person["name"],
            "start_time": minutes_to_str(start),
            "end_time": minutes_to_str(end),
        }] + sub[3]
        candidate = (count, end_time, total_travel, itinerary)
        if better_solution(candidate, best):
            best = candidate
    return best

# Prepare full remaining mask
remaining_mask = 0
for i in range(len(people)):
    remaining_mask |= (1 << i)

best_count, best_end, best_travel, best_itin = dfs(start_location, start_time, remaining_mask)

result = {"itinerary": best_itin}
print(json.dumps(result, ensure_ascii=False))