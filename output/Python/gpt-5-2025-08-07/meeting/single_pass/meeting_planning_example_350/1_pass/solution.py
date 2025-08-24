"""SOLUTION:"""
import json
import itertools
from copy import deepcopy

# Helper functions
def time_to_minutes(h, m):
    return h * 60 + m

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Input variables
start_location = "Bayview"
start_time = time_to_minutes(9, 0)  # 9:00

# Travel times (in minutes), directed
travel = {
    "Bayview": {
        "Pacific Heights": 23, "Mission District": 13, "Haight-Ashbury": 19, "Financial District": 19
    },
    "Pacific Heights": {
        "Bayview": 22, "Mission District": 15, "Haight-Ashbury": 11, "Financial District": 13
    },
    "Mission District": {
        "Bayview": 15, "Pacific Heights": 16, "Haight-Ashbury": 12, "Financial District": 17
    },
    "Haight-Ashbury": {
        "Bayview": 18, "Pacific Heights": 12, "Mission District": 11, "Financial District": 21
    },
    "Financial District": {
        "Bayview": 19, "Pacific Heights": 13, "Mission District": 17, "Haight-Ashbury": 19
    },
}

# People constraints
people = [
    {
        "name": "Mary",
        "location": "Pacific Heights",
        "window_start": time_to_minutes(10, 0),
        "window_end": time_to_minutes(19, 0),
        "min_duration": 45
    },
    {
        "name": "Lisa",
        "location": "Mission District",
        "window_start": time_to_minutes(20, 30),
        "window_end": time_to_minutes(22, 0),
        "min_duration": 75
    },
    {
        "name": "Betty",
        "location": "Haight-Ashbury",
        "window_start": time_to_minutes(7, 15),
        "window_end": time_to_minutes(17, 15),
        "min_duration": 90
    },
    {
        "name": "Charles",
        "location": "Financial District",
        "window_start": time_to_minutes(11, 15),
        "window_end": time_to_minutes(15, 0),
        "min_duration": 120
    },
]

people_by_name = {p["name"]: p for p in people}

def schedule_for_order(order):
    # Build base schedule with minimal durations
    itinerary = []
    cur_loc = start_location
    cur_time = start_time

    # For metric computation later
    base_records = []

    for person in order:
        p = people_by_name[person]
        t_travel = travel[cur_loc][p["location"]]
        arrival = cur_time + t_travel
        start = max(arrival, p["window_start"])
        end = start + p["min_duration"]
        if end > p["window_end"]:
            return None  # infeasible
        entry = {
            "person": p["name"],
            "location": p["location"],
            "start": start,
            "end": end
        }
        itinerary.append(entry)
        # For recalculations
        base_records.append({
            "arrival": arrival,
            "travel": t_travel
        })
        cur_loc = p["location"]
        cur_time = end

    # Extend meetings forward to soak up waiting (without delaying next meeting beyond its window_start)
    for i in range(len(itinerary) - 1):
        cur_meet = itinerary[i]
        next_meet = itinerary[i + 1]
        cur_p = people_by_name[cur_meet["person"]]
        next_p = people_by_name[next_meet["person"]]
        t_travel = travel[cur_p["location"]][next_p["location"]]
        arrival_next = cur_meet["end"] + t_travel
        next_window_start = next_p["window_start"]
        # Amount of waiting before next meeting if we leave now
        W = max(0, next_window_start - arrival_next)
        # Available time to extend current meeting
        available_extension = cur_p["window_end"] - cur_meet["end"]
        extend_by = min(W, available_extension)
        if extend_by > 0:
            cur_meet["end"] += extend_by
        # Ensure next meeting start remains valid (should still be max(arrival, window_start))
        # Recompute next start based on possibly updated arrival (still <= window_start)
        arrival_next_updated = cur_meet["end"] + t_travel
        next_meet["start"] = max(arrival_next_updated, next_p["window_start"])
        # Keep next meeting end at min duration from its (possibly recomputed) start
        next_meet["end"] = next_meet["start"] + people_by_name[next_meet["person"]]["min_duration"]
        if next_meet["end"] > next_p["window_end"]:
            return None  # infeasible after extension (shouldn't happen with our conservative extension)

    # Finally, extend the last meeting to its window end to maximize total meeting time
    if itinerary:
        last = itinerary[-1]
        last_p = people_by_name[last["person"]]
        last["end"] = min(last_p["window_end"], last["end"] + (last_p["window_end"] - last["end"]))

    # Compute metrics
    total_wait = 0
    total_travel = 0
    total_meeting = 0
    prev_loc = start_location
    prev_end = start_time

    for meet in itinerary:
        t_travel = travel[prev_loc][meet["location"]]
        total_travel += t_travel
        arrival = prev_end + t_travel
        wait = max(0, meet["start"] - arrival)
        total_wait += wait
        duration = meet["end"] - meet["start"]
        total_meeting += duration
        prev_loc = meet["location"]
        prev_end = meet["end"]

    return {
        "itinerary": itinerary,
        "metrics": {
            "count": len(itinerary),
            "total_wait": total_wait,
            "total_travel": total_travel,
            "total_meeting": total_meeting,
            "finish_time": prev_end
        }
    }

def compare_schedules(a, b):
    # Return True if a is better than b
    if b is None:
        return True
    am, bm = a["metrics"], b["metrics"]
    # Primary: maximize number of meetings
    if am["count"] != bm["count"]:
        return am["count"] > bm["count"]
    # Secondary: minimize total waiting time
    if am["total_wait"] != bm["total_wait"]:
        return am["total_wait"] < bm["total_wait"]
    # Tertiary: maximize total meeting time
    if am["total_meeting"] != bm["total_meeting"]:
        return am["total_meeting"] > bm["total_meeting"]
    # Quaternary: minimize total travel time
    if am["total_travel"] != bm["total_travel"]:
        return am["total_travel"] < bm["total_travel"]
    # Finally: earliest finish
    return am["finish_time"] < bm["finish_time"]

# Explore all subsets (from largest to smallest), and all permutations within each subset
best = None
names = [p["name"] for p in people]
for r in range(len(names), 0, -1):
    for order in itertools.permutations(names, r):
        sch = schedule_for_order(order)
        if sch is not None and compare_schedules(sch, best):
            best = sch
    if best and best["metrics"]["count"] == r:
        # Found feasible schedules of this size; no need to consider smaller subsets
        break

# Prepare JSON output
output = {"itinerary": []}
if best:
    for m in best["itinerary"]:
        output["itinerary"].append({
            "action": "meet",
            "location": m["location"],
            "person": m["person"],
            "start_time": minutes_to_str(m["start"]),
            "end_time": minutes_to_str(m["end"])
        })

print(json.dumps(output))