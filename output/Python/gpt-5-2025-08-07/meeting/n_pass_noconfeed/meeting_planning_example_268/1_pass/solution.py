# SOLUTION:
import json
from itertools import permutations, combinations

# -----------------------------
# Input parameters
# -----------------------------
start_location = "Golden Gate Park"
start_time_str = "9:00"

# Travel times in minutes (directed)
travel_minutes = {
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Presidio"): 18,
    ("Alamo Square", "Russian Hill"): 13,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
}

# Friend availability windows and minimum durations (in minutes)
friends_data = [
    {
        "name": "Timothy",
        "location": "Alamo Square",
        "window_start": "12:00",
        "window_end": "16:15",
        "min_duration": 105,
    },
    {
        "name": "Mark",
        "location": "Presidio",
        "window_start": "18:45",
        "window_end": "21:00",
        "min_duration": 60,
    },
    {
        "name": "Joseph",
        "location": "Russian Hill",
        "window_start": "16:45",
        "window_end": "21:30",
        "min_duration": 60,
    },
]

# -----------------------------
# Helper functions
# -----------------------------
def parse_time(s):
    h, m = s.split(":")
    return int(h) * 60 + int(m)

def time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def travel_time(a, b):
    return travel_minutes[(a, b)]

# -----------------------------
# Preprocess inputs
# -----------------------------
start_time = parse_time(start_time_str)

friends = []
for f in friends_data:
    friends.append({
        "name": f["name"],
        "location": f["location"],
        "ws": parse_time(f["window_start"]),
        "we": parse_time(f["window_end"]),
        "min": f["min_duration"],
    })

# -----------------------------
# Scheduling logic
# -----------------------------
def schedule_for_order(order):
    n = len(order)
    if n == 0:
        return None

    # Extract arrays for convenience
    locs = [p["location"] for p in order]
    ws = [p["ws"] for p in order]
    we = [p["we"] for p in order]
    mind = [p["min"] for p in order]

    # Backward pass: compute latest feasible start/end times given downstream constraints
    latest_start = [0] * n
    latest_end = [0] * n

    latest_start[-1] = we[-1] - mind[-1]
    latest_end[-1] = latest_start[-1] + mind[-1]
    for i in range(n - 2, -1, -1):
        t_to_next = travel_time(locs[i], locs[i + 1])
        latest_end[i] = min(we[i], latest_start[i + 1] - t_to_next)
        latest_start[i] = latest_end[i] - mind[i]

    # If any meeting cannot fit even at latest placement, infeasible
    for i in range(n):
        if latest_end[i] < ws[i] + mind[i]:
            return None

    # Forward pass: compute earliest feasible starts using minimal durations
    s = [0] * n
    e = [0] * n

    cur_loc = start_location
    cur_time = start_time
    for i in range(n):
        arr_if_now = cur_time + travel_time(cur_loc, locs[i])
        s[i] = max(ws[i], arr_if_now)
        e[i] = s[i] + mind[i]
        # Feasibility check against latest_start
        if s[i] > latest_start[i]:
            return None
        cur_loc = locs[i]
        cur_time = e[i]

    # Extension to reduce waiting before next meeting while staying feasible
    for i in range(n - 1):
        t_to_next = travel_time(locs[i], locs[i + 1])
        arrival_next = e[i] + t_to_next
        wait_before_next = max(0, ws[i + 1] - arrival_next)
        slack_here = max(0, latest_end[i] - e[i])
        extend = min(wait_before_next, slack_here)
        if extend > 0:
            e[i] += extend
        # Recompute next meeting start based on new arrival
        arrival_next = e[i] + t_to_next
        s[i + 1] = max(ws[i + 1], arrival_next)
        e[i + 1] = s[i + 1] + mind[i + 1]
        # If this pushes next beyond its latest feasible start, infeasible
        if s[i + 1] > latest_start[i + 1]:
            return None

    # Compute metrics: total idle time and total travel time
    idle = 0
    total_travel = 0
    cur_loc = start_location
    cur_time = start_time
    for i in range(n):
        tmove = travel_time(cur_loc, locs[i])
        depart_time = s[i] - tmove
        if depart_time > cur_time:
            idle += depart_time - cur_time
        cur_time = depart_time + tmove  # arrival equals s[i]
        total_travel += tmove
        cur_time = e[i]  # after meeting
        cur_loc = locs[i]

    finish_time = e[-1]

    # Build itinerary
    itinerary = []
    for i in range(n):
        itinerary.append({
            "action": "meet",
            "location": locs[i],
            "person": order[i]["name"],
            "start_time": time_str(s[i]),
            "end_time": time_str(e[i]),
        })

    return {
        "itinerary": itinerary,
        "count": n,
        "idle": idle,
        "travel": total_travel,
        "finish": finish_time,
    }

def better(a, b):
    # Choose better schedule: more friends -> less idle -> less travel -> earlier finish
    if a is None:
        return b
    if b is None:
        return a
    if b["count"] > a["count"]:
        return b
    if b["count"] < a["count"]:
        return a
    if b["idle"] < a["idle"]:
        return b
    if b["idle"] > a["idle"]:
        return a
    if b["travel"] < a["travel"]:
        return b
    if b["travel"] > a["travel"]:
        return a
    if b["finish"] < a["finish"]:
        return b
    if b["finish"] > a["finish"]:
        return a
    # Stable: keep existing
    return a

# -----------------------------
# Explore schedules
# -----------------------------
best = None
n = len(friends)
# Search from largest subset to smallest
for k in range(n, 0, -1):
    for subset in combinations(friends, k):
        for order in permutations(subset):
            plan = schedule_for_order(list(order))
            best = better(best, plan)
    if best and best["count"] == k:
        # Found the best possible count for this k; no need to check smaller subsets
        break

# -----------------------------
# Output result
# -----------------------------
output = {"itinerary": best["itinerary"] if best else []}
print(json.dumps(output, ensure_ascii=False))