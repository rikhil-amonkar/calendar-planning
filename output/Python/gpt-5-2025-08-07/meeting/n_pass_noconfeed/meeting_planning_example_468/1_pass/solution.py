import itertools
import json

def time_to_minutes(h, m):
    return h * 60 + m

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Input parameters and constraints
start_location = "The Castro"
start_time = time_to_minutes(9, 0)  # 9:00

min_meet_minutes = 90

people = [
    {"name": "Rebecca", "location": "Bayview", "start": time_to_minutes(9, 0), "end": time_to_minutes(12, 45)},
    {"name": "Amanda", "location": "Pacific Heights", "start": time_to_minutes(18, 30), "end": time_to_minutes(21, 45)},
    {"name": "James", "location": "Alamo Square", "start": time_to_minutes(9, 45), "end": time_to_minutes(21, 15)},
    {"name": "Sarah", "location": "Fisherman's Wharf", "start": time_to_minutes(8, 0), "end": time_to_minutes(21, 30)},
    {"name": "Melissa", "location": "Golden Gate Park", "start": time_to_minutes(9, 0), "end": time_to_minutes(18, 45)},
]

# Travel times (minutes)
locations = [
    "The Castro",
    "Bayview",
    "Pacific Heights",
    "Alamo Square",
    "Fisherman's Wharf",
    "Golden Gate Park",
]

dist = {loc: {loc2: None for loc2 in locations} for loc in locations}
for loc in locations:
    dist[loc][loc] = 0

# Given distances
dist["The Castro"]["Bayview"] = 19
dist["The Castro"]["Pacific Heights"] = 16
dist["The Castro"]["Alamo Square"] = 8
dist["The Castro"]["Fisherman's Wharf"] = 24
dist["The Castro"]["Golden Gate Park"] = 11

dist["Bayview"]["The Castro"] = 20
dist["Bayview"]["Pacific Heights"] = 23
dist["Bayview"]["Alamo Square"] = 16
dist["Bayview"]["Fisherman's Wharf"] = 25
dist["Bayview"]["Golden Gate Park"] = 22

dist["Pacific Heights"]["The Castro"] = 16
dist["Pacific Heights"]["Bayview"] = 22
dist["Pacific Heights"]["Alamo Square"] = 10
dist["Pacific Heights"]["Fisherman's Wharf"] = 13
dist["Pacific Heights"]["Golden Gate Park"] = 15

dist["Alamo Square"]["The Castro"] = 8
dist["Alamo Square"]["Bayview"] = 16
dist["Alamo Square"]["Pacific Heights"] = 10
dist["Alamo Square"]["Fisherman's Wharf"] = 19
dist["Alamo Square"]["Golden Gate Park"] = 9

dist["Fisherman's Wharf"]["The Castro"] = 26
dist["Fisherman's Wharf"]["Bayview"] = 26
dist["Fisherman's Wharf"]["Pacific Heights"] = 12
dist["Fisherman's Wharf"]["Alamo Square"] = 20
dist["Fisherman's Wharf"]["Golden Gate Park"] = 25

dist["Golden Gate Park"]["The Castro"] = 13
dist["Golden Gate Park"]["Bayview"] = 23
dist["Golden Gate Park"]["Pacific Heights"] = 16
dist["Golden Gate Park"]["Alamo Square"] = 10
dist["Golden Gate Park"]["Fisherman's Wharf"] = 24

# Validate that all needed distances are present
for a in locations:
    for b in locations:
        if dist[a][b] is None:
            raise ValueError(f"Missing distance from {a} to {b}")

def simulate_schedule(order):
    itinerary = []
    current_loc = start_location
    current_time = start_time
    total_wait = 0
    total_travel = 0

    for person in order:
        travel = dist[current_loc][person["location"]]
        total_travel += travel
        arrival = current_time + travel
        start = max(arrival, person["start"])
        wait = max(0, start - arrival)
        total_wait += wait
        end = start + min_meet_minutes
        if end > person["end"]:
            return None  # infeasible
        itinerary.append({
            "action": "meet",
            "location": person["location"],
            "person": person["name"],
            "start_time": minutes_to_str(start),
            "end_time": minutes_to_str(end),
        })
        current_time = end
        current_loc = person["location"]

    finish_time = current_time
    return {
        "itinerary": itinerary,
        "finish_time": finish_time,
        "total_wait": total_wait,
        "total_travel": total_travel,
        "count": len(order),
    }

def better(a, b):
    # Returns True if a is better than b under our objectives
    if b is None:
        return True
    # Primary: maximize meetings count
    if a["count"] != b["count"]:
        return a["count"] > b["count"]
    # Secondary: minimize finish time
    if a["finish_time"] != b["finish_time"]:
        return a["finish_time"] < b["finish_time"]
    # Tertiary: minimize total wait
    if a["total_wait"] != b["total_wait"]:
        return a["total_wait"] < b["total_wait"]
    # Then minimize total travel
    if a["total_travel"] != b["total_travel"]:
        return a["total_travel"] < b["total_travel"]
    # Tie-breaker: lexicographically by itinerary for determinism
    ita = [(i["person"], i["start_time"], i["end_time"]) for i in a["itinerary"]]
    itb = [(i["person"], i["start_time"], i["end_time"]) for i in b["itinerary"]]
    return ita < itb

best = None
N = len(people)

# Explore subsets from largest to smallest; for a given size, consider all permutations
for size in range(N, 0, -1):
    any_feasible = False
    for subset in itertools.combinations(people, size):
        for perm in itertools.permutations(subset):
            result = simulate_schedule(perm)
            if result is not None:
                any_feasible = True
                if better(result, best):
                    best = result
    if any_feasible:
        break  # Found the maximum number of meetings achievable

# Prepare output
output = {"itinerary": []}
if best is not None:
    output["itinerary"] = best["itinerary"]

print(json.dumps(output, ensure_ascii=False))