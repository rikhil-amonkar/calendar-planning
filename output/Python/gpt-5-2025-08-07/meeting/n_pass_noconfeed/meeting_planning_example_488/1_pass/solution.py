# SOLUTION:
import json
import itertools

def time_to_minutes(t):
    # t like '9:00' or '13:30'
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mins = m % 60
    return f"{h}:{mins:02d}"

# Input variables
start_location = "Pacific Heights"
arrival_time_str = "9:00"

people = {
    "Ronald": {
        "location": "Nob Hill",
        "start": "10:00",
        "end": "17:00",
        "min_duration": 105
    },
    "Sarah": {
        "location": "Russian Hill",
        "start": "7:15",
        "end": "9:30",
        "min_duration": 45
    },
    "Helen": {
        "location": "The Castro",
        "start": "13:30",
        "end": "17:00",
        "min_duration": 120
    },
    "Joshua": {
        "location": "Sunset District",
        "start": "14:15",
        "end": "19:30",
        "min_duration": 90
    },
    "Margaret": {
        "location": "Haight-Ashbury",
        "start": "10:15",
        "end": "22:00",
        "min_duration": 60
    },
}

# Directed travel times (in minutes)
travel_times = {
    "Pacific Heights": {
        "Nob Hill": 8,
        "Russian Hill": 7,
        "The Castro": 16,
        "Sunset District": 21,
        "Haight-Ashbury": 11
    },
    "Nob Hill": {
        "Pacific Heights": 8,
        "Russian Hill": 5,
        "The Castro": 17,
        "Sunset District": 25,
        "Haight-Ashbury": 13
    },
    "Russian Hill": {
        "Pacific Heights": 7,
        "Nob Hill": 5,
        "The Castro": 21,
        "Sunset District": 23,
        "Haight-Ashbury": 17
    },
    "The Castro": {
        "Pacific Heights": 16,
        "Nob Hill": 16,
        "Russian Hill": 18,
        "Sunset District": 17,
        "Haight-Ashbury": 6
    },
    "Sunset District": {
        "Pacific Heights": 21,
        "Nob Hill": 27,
        "Russian Hill": 24,
        "The Castro": 17,
        "Haight-Ashbury": 15
    },
    "Haight-Ashbury": {
        "Pacific Heights": 12,
        "Nob Hill": 15,
        "Russian Hill": 17,
        "The Castro": 6,
        "Sunset District": 15
    }
}

# Helper to get travel time; 0 if same location
def get_travel(a, b):
    if a == b:
        return 0
    return travel_times[a][b]

# Pre-process times
arrival_time = time_to_minutes(arrival_time_str)
for p in people.values():
    p["start_min"] = time_to_minutes(p["start"])
    p["end_min"] = time_to_minutes(p["end"])

names = list(people.keys())

def evaluate_schedule(order):
    current_loc = start_location
    current_time = arrival_time
    itinerary = []
    total_travel = 0
    total_wait = 0

    for name in order:
        p = people[name]
        # Travel
        travel = get_travel(current_loc, p["location"])
        current_time += travel
        total_travel += travel

        # Wait if early
        if current_time < p["start_min"]:
            total_wait += p["start_min"] - current_time
            current_time = p["start_min"]

        # Determine end of meeting
        meeting_start = current_time
        meeting_end = meeting_start + p["min_duration"]

        # Check availability window
        if meeting_end > p["end_min"]:
            return None  # infeasible

        # Record meeting
        itinerary.append({
            "action": "meet",
            "location": p["location"],
            "person": name,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })

        # Update state
        current_time = meeting_end
        current_loc = p["location"]

    finish_time = current_time
    return {
        "itinerary": itinerary,
        "finish_time": finish_time,
        "total_travel": total_travel,
        "total_wait": total_wait
    }

best = None

# Objective comparison
def better(a, b):
    # a is better than b?
    if b is None:
        return True
    # More meetings
    if len(a["itinerary"]) != len(b["itinerary"]):
        return len(a["itinerary"]) > len(b["itinerary"])
    # Earlier finish time
    if a["finish_time"] != b["finish_time"]:
        return a["finish_time"] < b["finish_time"]
    # Less total idle + travel
    a_cost = a["total_travel"] + a["total_wait"]
    b_cost = b["total_travel"] + b["total_wait"]
    if a_cost != b_cost:
        return a_cost < b_cost
    # Arbitrary tie-breaker: lexicographic by names
    return [m["person"] for m in a["itinerary"]] < [m["person"] for m in b["itinerary"]]

# Explore all subsets and permutations
for r in range(1, len(names) + 1):
    for subset in itertools.combinations(names, r):
        for perm in itertools.permutations(subset):
            result = evaluate_schedule(perm)
            if result is not None:
                if better(result, best):
                    best = result

# If no feasible meetings at all, return empty itinerary
output = {"itinerary": best["itinerary"] if best else []}

print(json.dumps(output, ensure_ascii=False, indent=2))