import json
from itertools import permutations, combinations

# -------------------------------
# Input parameters (constraints)
# -------------------------------

start_location = "Nob Hill"
start_time_str = "9:00"

# Travel times (directed, in minutes)
travel_times = {
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Pacific Heights"): 11,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Pacific Heights"): 8,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
}

# Friend availability and minimum meeting durations
friends = [
    {
        "name": "Jeffrey",
        "location": "Presidio",
        "start": "8:00",
        "end": "10:00",
        "min_minutes": 105
    },
    {
        "name": "Steven",
        "location": "North Beach",
        "start": "13:30",
        "end": "22:00",
        "min_minutes": 45
    },
    {
        "name": "Barbara",
        "location": "Fisherman's Wharf",
        "start": "18:00",
        "end": "21:30",
        "min_minutes": 30
    },
    {
        "name": "John",
        "location": "Pacific Heights",
        "start": "9:00",
        "end": "13:30",
        "min_minutes": 15
    },
]

# -------------------------------
# Helper functions
# -------------------------------

def parse_time(tstr):
    # tstr like '9:00' or '13:30'
    h, m = tstr.split(":")
    return int(h) * 60 + int(m)

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def get_travel(a, b):
    if (a, b) not in travel_times:
        raise ValueError(f"No travel time from {a} to {b}")
    return travel_times[(a, b)]

# -------------------------------
# Prepare data
# -------------------------------

start_time = parse_time(start_time_str)

# Convert friend times to minutes
friend_objs = []
for f in friends:
    friend_objs.append({
        "name": f["name"],
        "location": f["location"],
        "start": parse_time(f["start"]),
        "end": parse_time(f["end"]),
        "min_minutes": f["min_minutes"]
    })

# -------------------------------
# Scheduling logic
# -------------------------------

def build_schedule(order):
    """
    Given an ordered list of friend dicts, build the earliest-feasible schedule that:
    - Meets each person for at least their minimum duration within their availability window
    - Accounts for travel times
    - Greedily extends each meeting (when possible) to reduce waiting before the next meeting
    Returns (feasible, itinerary, end_time, total_wait, total_travel)
    """
    itinerary = []
    current_loc = start_location
    current_time = start_time
    total_wait = 0
    total_travel = 0

    for i, f in enumerate(order):
        # Travel to meeting location
        travel = get_travel(current_loc, f["location"])
        total_travel += travel
        arrival = current_time + travel

        # Start time must be within window
        start = max(arrival, f["start"])

        # Wait if arrived early
        wait = max(0, start - arrival)
        total_wait += wait

        # Earliest end respecting minimum duration
        end = start + f["min_minutes"]
        if end > f["end"]:
            return False, None, None, None, None  # infeasible

        # If there is a next meeting, greedily extend current meeting to reduce waiting later
        if i < len(order) - 1:
            nxt = order[i + 1]
            travel_next = get_travel(f["location"], nxt["location"])
            # We can extend end up to f["end"]
            # We want arrival at next to be no earlier than next's window start
            # i.e., end + travel_next <= nxt["start"]
            additional = max(0, nxt["start"] - (end + travel_next))
            extend_by = min(additional, f["end"] - end)
            end += extend_by

        itinerary.append({
            "action": "meet",
            "location": f["location"],
            "person": f["name"],
            "start_time": format_time(start),
            "end_time": format_time(end),
        })

        current_loc = f["location"]
        current_time = end

    end_time = current_time
    return True, itinerary, end_time, total_wait, total_travel

# Objective:
# 1) Maximize number of friends met
# 2) Among those, minimize end_time
# 3) Then minimize total_wait
# 4) Then minimize total_travel
# 5) Deterministic tie-breaker on itinerary string

best = None  # tuple (score_tuple, itinerary)
best_itin = None

# Generate all subsets and permutations
n = len(friend_objs)
for r in range(n, 0, -1):  # try larger subsets first
    found_any_for_this_r = False
    for subset in combinations(friend_objs, r):
        for order in permutations(subset):
            feasible, itin, end_time, total_wait, total_travel = build_schedule(order)
            if not feasible:
                continue
            found_any_for_this_r = True
            score = (-r, end_time, total_wait, total_travel, json.dumps(itin, sort_keys=True))
            if best is None or score < best:
                best = score
                best_itin = itin
    if found_any_for_this_r:
        break  # since we iterate from largest r downwards, we can stop once we found feasible at this r

if best_itin is None:
    result = {"itinerary": []}
else:
    result = {"itinerary": best_itin}

print(json.dumps(result, indent=2))