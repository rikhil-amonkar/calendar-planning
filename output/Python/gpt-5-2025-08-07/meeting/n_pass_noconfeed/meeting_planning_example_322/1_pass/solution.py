"SOLUTION:"

import json
import itertools

def to_minutes(tstr):
    h, m = tstr.split(":")
    return int(h) * 60 + int(m)

def fmt_time(m):
    h = m // 60
    mn = m % 60
    return f"{h}:{mn:02d}"

# Input parameters
start_location = "Sunset District"
start_time_str = "9:00"
start_time = to_minutes(start_time_str)

# Travel times (directed, in minutes)
dist = {
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Presidio"): 17,
}

# Friends constraints
friends = [
    {
        "name": "William",
        "location": "Russian Hill",
        "window_start": to_minutes("18:30"),
        "window_end": to_minutes("20:45"),
        "min_duration": 105,
    },
    {
        "name": "Michelle",
        "location": "Chinatown",
        "window_start": to_minutes("8:15"),
        "window_end": to_minutes("14:00"),
        "min_duration": 15,
    },
    {
        "name": "George",
        "location": "Presidio",
        "window_start": to_minutes("10:30"),
        "window_end": to_minutes("18:45"),
        "min_duration": 30,
    },
    {
        "name": "Robert",
        "location": "Fisherman's Wharf",
        "window_start": to_minutes("9:00"),
        "window_end": to_minutes("13:45"),
        "min_duration": 30,
    },
]

# Helper to get travel time between two locations
def travel_time(a, b):
    if a == b:
        return 0
    try:
        return dist[(a, b)]
    except KeyError:
        raise KeyError(f"Missing travel time from {a} to {b}")

def evaluate_order(order):
    # Forward pass: compute earliest feasible schedule
    n = len(order)
    earliest_arrival = [None] * n
    earliest_start = [None] * n
    end_time = [None] * n

    cur_loc = start_location
    cur_time = start_time

    for i, person in enumerate(order):
        t = travel_time(cur_loc, person["location"])
        arrive = cur_time + t
        start_i = max(arrive, person["window_start"])
        end_i = start_i + person["min_duration"]
        if end_i > person["window_end"]:
            return None  # infeasible

        earliest_arrival[i] = arrive
        earliest_start[i] = start_i
        end_time[i] = end_i

        cur_loc = person["location"]
        cur_time = end_i

    # Backward pass: push meetings as late as possible while keeping last at its earliest feasible start
    start_times = earliest_start[:]
    end_times = [start_times[i] + order[i]["min_duration"] for i in range(n)]

    # Keep last meeting at earliest feasible start (for minimal final end time)
    # Already set in start_times[-1]

    for i in range(n - 2, -1, -1):
        next_loc = order[i + 1]["location"]
        this_loc = order[i]["location"]
        t = travel_time(this_loc, next_loc)
        target_arrival = start_times[i + 1] - t

        latest_end_allowed = min(order[i]["window_end"], target_arrival)
        latest_start_allowed = latest_end_allowed - order[i]["min_duration"]
        earliest_start_allowed = max(earliest_arrival[i], order[i]["window_start"])

        if latest_start_allowed < earliest_start_allowed:
            # If we cannot push late without breaking feasibility, fall back to earliest feasible
            start_i = earliest_start[i]
            end_i = end_time[i]
            # Double-check linkage still works
            if end_i + t > start_times[i + 1]:
                return None
        else:
            start_i = latest_start_allowed
            end_i = start_i + order[i]["min_duration"]

        start_times[i] = start_i
        end_times[i] = end_i

    # Compute totals for tie-breaking
    total_travel = 0
    total_wait = 0
    prev_loc = start_location
    prev_time = start_time
    for i, person in enumerate(order):
        t = travel_time(prev_loc, person["location"])
        total_travel += t
        arrival = prev_time + t
        wait = max(0, start_times[i] - arrival)
        total_wait += wait
        prev_loc = person["location"]
        prev_time = end_times[i]

    final_end = end_times[-1]
    return {
        "order": order,
        "starts": start_times,
        "ends": end_times,
        "total_travel": total_travel,
        "total_wait": total_wait,
        "final_end": final_end,
        "count": n,
    }

# Generate all feasible schedules across all subsets and permutations
best = None
people_indices = list(range(len(friends)))

# Consider all non-empty subsets
for r in range(len(friends), 0, -1):
    for subset in itertools.permutations(friends, r):
        result = evaluate_order(list(subset))
        if result is None:
            continue
        score = (-result["count"], result["final_end"], result["total_wait"], result["total_travel"])
        if best is None or score < best["score"]:
            best = {"score": score, "result": result}
    # Early exit if we found a solution that includes all friends
    if best and -best["score"][0] == len(friends):
        break

# Build itinerary JSON
itinerary = []
if best:
    res = best["result"]
    for person, s, e in zip(res["order"], res["starts"], res["ends"]):
        itinerary.append({
            "action": "meet",
            "location": person["location"],
            "person": person["name"],
            "start_time": fmt_time(s),
            "end_time": fmt_time(e),
        })

output = {"itinerary": itinerary}
print(json.dumps(output, ensure_ascii=False))