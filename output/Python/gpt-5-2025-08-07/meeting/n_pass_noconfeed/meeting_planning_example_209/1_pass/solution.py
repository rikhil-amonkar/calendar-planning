# SOLUTION:
import json
from itertools import permutations, combinations

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Input variables (meeting constraints and travel times)
start_location = "Sunset District"
start_time_str = "9:00"

travel_times = {
    "Sunset District": {"Chinatown": 30, "Russian Hill": 24, "North Beach": 29},
    "Chinatown": {"Sunset District": 29, "Russian Hill": 7, "North Beach": 3},
    "Russian Hill": {"Sunset District": 23, "Chinatown": 9, "North Beach": 5},
    "North Beach": {"Sunset District": 27, "Chinatown": 6, "Russian Hill": 4},
}

people = {
    "Anthony": {
        "location": "Chinatown",
        "window_start": "13:15",
        "window_end": "14:30",
        "min_duration_min": 60,
    },
    "Rebecca": {
        "location": "Russian Hill",
        "window_start": "19:30",
        "window_end": "21:15",
        "min_duration_min": 105,
    },
    "Melissa": {
        "location": "North Beach",
        "window_start": "8:15",
        "window_end": "13:30",
        "min_duration_min": 105,
    },
}

# Preprocess times into minutes
start_time = to_minutes(start_time_str)
for name, p in people.items():
    p["start"] = to_minutes(p["window_start"])
    p["end"] = to_minutes(p["window_end"])
    p["dur"] = p["min_duration_min"]

def build_schedule(order):
    schedule = []
    current_loc = start_location
    current_time = start_time
    prev_name = None

    for name in order:
        p = people[name]
        travel = travel_times[current_loc][p["location"]]

        # Try extending previous meeting to reduce waiting for this meeting (if possible)
        if prev_name is not None:
            prev_p = people[prev_name]
            arrival_if_leave_now = current_time + travel
            if arrival_if_leave_now < p["start"]:
                # We can extend the previous meeting up to its window end to reduce waiting
                max_extend = prev_p["end"] - current_time
                need_extend = p["start"] - arrival_if_leave_now
                extend_by = min(max(0, need_extend), max(0, max_extend))
                if extend_by > 0:
                    # Extend previous meeting end time
                    schedule[-1]["end"] += extend_by
                    current_time += extend_by

        # Compute arrival and schedule this meeting at earliest feasible time
        arrival = current_time + travel
        meeting_start = max(arrival, p["start"])
        meeting_end = meeting_start + p["dur"]
        if meeting_end > p["end"]:
            return None  # infeasible
        schedule.append({
            "person": name,
            "location": p["location"],
            "start": meeting_start,
            "end": meeting_end
        })
        current_loc = p["location"]
        current_time = meeting_end
        prev_name = name

    return schedule

def compute_idle(schedule):
    idle = 0
    time = start_time
    loc = start_location
    for item in schedule:
        travel = travel_times[loc][item["location"]]
        arrival = time + travel
        if item["start"] > arrival:
            idle += item["start"] - arrival
        time = item["end"]
        loc = item["location"]
    return idle

def compute_travel(schedule):
    total = 0
    time = start_time
    loc = start_location
    for item in schedule:
        total += travel_times[loc][item["location"]]
        time = item["end"]
        loc = item["location"]
    return total

# Search for the optimal schedule:
# Primary objective: meet as many friends as possible.
# Tie-breaker 1: minimize total idle time.
# Tie-breaker 2: earliest finish time.
# Tie-breaker 3: minimal total travel time.
names = list(people.keys())
best = None

# Try subsets in descending size
for r in range(len(names), -1, -1):
    found_any = False
    for subset in combinations(names, r):
        for order in permutations(subset):
            sched = build_schedule(order)
            if sched is None:
                continue
            found_any = True
            idle = compute_idle(sched)
            finish = sched[-1]["end"] if sched else start_time
            travel_sum = compute_travel(sched)

            candidate = {
                "schedule": sched,
                "count": len(sched),
                "idle": idle,
                "finish": finish,
                "travel": travel_sum
            }

            if best is None:
                best = candidate
            else:
                if candidate["count"] > best["count"]:
                    best = candidate
                elif candidate["count"] == best["count"]:
                    if candidate["idle"] < best["idle"]:
                        best = candidate
                    elif candidate["idle"] == best["idle"]:
                        if candidate["finish"] < best["finish"]:
                            best = candidate
                        elif candidate["finish"] == best["finish"]:
                            if candidate["travel"] < best["travel"]:
                                best = candidate
    if found_any and best and best["count"] == r:
        break  # No need to check smaller subsets if we already have a feasible one of this size

# Prepare JSON output
output = {"itinerary": []}
if best and best["schedule"]:
    for item in best["schedule"]:
        output["itinerary"].append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": minutes_to_str(item["start"]),
            "end_time": minutes_to_str(item["end"]),
        })

print(json.dumps(output, ensure_ascii=False))