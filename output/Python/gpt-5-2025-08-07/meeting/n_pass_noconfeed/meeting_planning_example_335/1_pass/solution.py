import itertools
import json

def time_to_min(tstr):
    # expects 'H:MM' 24h format
    h, m = tstr.split(':')
    return int(h) * 60 + int(m)

def min_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Input variables
start_location = "Pacific Heights"
arrival_time_str = "9:00"

travel_minutes = {
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Mission District"): 15,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Mission District"): 18,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Mission District"): 17,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Mission District"): 10,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Financial District"): 17,
    ("Mission District", "Alamo Square"): 11,
}

people = {
    "Helen": {
        "location": "North Beach",
        "window_start": "9:00",
        "window_end": "17:00",
        "min_minutes": 15,
    },
    "Betty": {
        "location": "Financial District",
        "window_start": "19:00",
        "window_end": "21:45",
        "min_minutes": 90,
    },
    "Amanda": {
        "location": "Alamo Square",
        "window_start": "19:45",
        "window_end": "21:00",
        "min_minutes": 60,
    },
    "Kevin": {
        "location": "Mission District",
        "window_start": "10:45",
        "window_end": "14:45",
        "min_minutes": 45,
    },
}

# Convert time strings to minutes
arrival_time = time_to_min(arrival_time_str)
for p in people.values():
    p["start_min"] = time_to_min(p["window_start"])
    p["end_min"] = time_to_min(p["window_end"])

def simulate(order):
    current_loc = start_location
    current_time = arrival_time
    itinerary = []
    total_travel = 0

    for name in order:
        person = people[name]
        loc = person["location"]
        # travel
        travel = travel_minutes[(current_loc, loc)]
        total_travel += travel
        arrive = current_time + travel

        # wait if early
        meeting_start = max(arrive, person["start_min"])
        meeting_end = meeting_start + person["min_minutes"]

        # check feasibility within window
        if meeting_end > person["end_min"]:
            return None  # infeasible

        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": min_to_time(meeting_start),
            "end_time": min_to_time(meeting_end),
        })

        # update state
        current_loc = loc
        current_time = meeting_end

    return {
        "itinerary": itinerary,
        "end_time": current_time,
        "total_travel": total_travel,
        "count": len(order),
        "order": order,
    }

# Search over all subsets and orders to maximize number of friends met
names = list(people.keys())
best = None

for r in range(len(names), 0, -1):  # try largest subsets first
    candidates = []
    for subset in itertools.combinations(names, r):
        for perm in itertools.permutations(subset):
            result = simulate(perm)
            if result is not None:
                candidates.append(result)
    if candidates:
        # Choose best by:
        # 1) earliest end_time
        # 2) minimal total_travel
        # 3) lexicographically smallest order (deterministic)
        candidates.sort(key=lambda x: (x["end_time"], x["total_travel"], list(x["order"])))
        best = candidates[0]
        break

output = {"itinerary": best["itinerary"] if best else []}
print(json.dumps(output, ensure_ascii=False))