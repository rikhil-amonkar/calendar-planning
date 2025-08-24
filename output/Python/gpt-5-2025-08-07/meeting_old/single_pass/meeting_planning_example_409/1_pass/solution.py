import itertools
import json

def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Input data
start_location = "Fisherman's Wharf"
start_time_str = "9:00"
start_time = time_to_minutes(start_time_str)

# Travel times (directed, minutes)
travel = {
    "Fisherman's Wharf": {
        "Bayview": 26, "Golden Gate Park": 25, "Nob Hill": 11, "Marina District": 9, "Embarcadero": 8
    },
    "Bayview": {
        "Fisherman's Wharf": 25, "Golden Gate Park": 22, "Nob Hill": 20, "Marina District": 25, "Embarcadero": 19
    },
    "Golden Gate Park": {
        "Fisherman's Wharf": 24, "Bayview": 23, "Nob Hill": 20, "Marina District": 16, "Embarcadero": 25
    },
    "Nob Hill": {
        "Fisherman's Wharf": 11, "Bayview": 19, "Golden Gate Park": 17, "Marina District": 11, "Embarcadero": 9
    },
    "Marina District": {
        "Fisherman's Wharf": 10, "Bayview": 27, "Golden Gate Park": 18, "Nob Hill": 12, "Embarcadero": 14
    },
    "Embarcadero": {
        "Fisherman's Wharf": 6, "Bayview": 21, "Golden Gate Park": 25, "Nob Hill": 10, "Marina District": 12
    }
}

# Friends constraints
friends = [
    {
        "person": "Thomas",
        "location": "Bayview",
        "avail_start": time_to_minutes("15:30"),
        "avail_end": time_to_minutes("18:30"),
        "min_duration": 120
    },
    {
        "person": "Stephanie",
        "location": "Golden Gate Park",
        "avail_start": time_to_minutes("18:30"),
        "avail_end": time_to_minutes("21:45"),
        "min_duration": 30
    },
    {
        "person": "Laura",
        "location": "Nob Hill",
        "avail_start": time_to_minutes("8:45"),
        "avail_end": time_to_minutes("16:15"),
        "min_duration": 30
    },
    {
        "person": "Betty",
        "location": "Marina District",
        "avail_start": time_to_minutes("18:45"),
        "avail_end": time_to_minutes("21:45"),
        "min_duration": 45
    },
    {
        "person": "Patricia",
        "location": "Embarcadero",
        "avail_start": time_to_minutes("17:30"),
        "avail_end": time_to_minutes("22:00"),
        "min_duration": 45
    }
]

# Helper to simulate minimal schedule feasibility for an order
def simulate_minimal(order):
    current_loc = start_location
    current_time = start_time
    schedule = []
    for f in order:
        t = travel[current_loc][f["location"]]
        arrival = current_time + t
        start = max(arrival, f["avail_start"])
        end = start + f["min_duration"]
        if end > f["avail_end"]:
            return None  # infeasible
        schedule.append({
            "person": f["person"],
            "location": f["location"],
            "start_min": start,
            "end_min": end
        })
        current_loc = f["location"]
        current_time = end
    return schedule

# Compute latest feasible start times backward for minimal durations
def compute_latest_starts(order):
    n = len(order)
    latest_start = [None] * n
    # Last meeting latest start is avail_end - min_duration
    last = order[-1]
    latest_start[-1] = last["avail_end"] - last["min_duration"]
    # Backward for others
    for i in range(n - 2, -1, -1):
        f = order[i]
        next_f = order[i + 1]
        travel_time = travel[f["location"]][next_f["location"]]
        option1 = f["avail_end"] - f["min_duration"]
        option2 = latest_start[i + 1] - travel_time - f["min_duration"]
        latest_start[i] = min(option1, option2)
        # Feasibility quick check: latest_start should not be before availability start
        if latest_start[i] < f["avail_start"]:
            # Infeasible sequence under minimal constraints
            return None
    # Also ensure last latest_start is not before last avail start
    if latest_start[-1] < order[-1]["avail_start"]:
        return None
    return latest_start

# Expand schedule to maximize total meeting time given latest starts
def expand_schedule(order, latest_start):
    n = len(order)
    # max_end for each meeting
    max_end = [None] * n
    for i in range(n):
        max_end[i] = latest_start[i] + order[i]["min_duration"] if i < n else order[i]["avail_end"]
    # Forward schedule using max_end
    itinerary = []
    current_loc = start_location
    current_time = start_time
    total_meet = 0
    for i, f in enumerate(order):
        t = travel[current_loc][f["location"]]
        arrival = current_time + t
        start = max(arrival, f["avail_start"])
        end = max_end[i]
        if end > f["avail_end"]:
            end = f["avail_end"]
        if start > end:
            return None, None, None  # infeasible
        itinerary.append({
            "action": "meet",
            "location": f["location"],
            "person": f["person"],
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
        total_meet += (end - start)
        current_loc = f["location"]
        current_time = end
    return itinerary, total_meet, current_time

# Search for optimal schedule
best_itinerary = None
best_count = -1
best_total_meet = -1
best_finish_time = None

# Sort friends into a stable list for deterministic combinations
friends_by_name = sorted(friends, key=lambda x: x["person"])

N = len(friends_by_name)
found_any = False

for r in range(N, 0, -1):
    feasible_options = []
    for subset in itertools.combinations(friends_by_name, r):
        for perm in itertools.permutations(subset):
            min_sched = simulate_minimal(perm)
            if min_sched is None:
                continue
            latest_start = compute_latest_starts(perm)
            if latest_start is None:
                continue
            itinerary, total_meet, finish_time = expand_schedule(perm, latest_start)
            if itinerary is None:
                continue
            feasible_options.append((itinerary, total_meet, finish_time))
    if feasible_options:
        # Choose the best among these: maximize total_meet, then minimize finish_time
        feasible_options.sort(key=lambda x: (-x[1], x[2]))
        best_itinerary, best_total_meet, best_finish_time = feasible_options[0]
        best_count = r
        found_any = True
        break

# If none found (shouldn't happen), produce empty itinerary
result = {
    "itinerary": best_itinerary if found_any else []
}

print(json.dumps(result, ensure_ascii=False))