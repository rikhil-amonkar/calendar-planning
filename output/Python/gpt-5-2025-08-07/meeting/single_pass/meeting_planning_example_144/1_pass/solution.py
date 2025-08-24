"""SOLUTION:"""
import json
from itertools import permutations

def parse_time(tstr):
    h, m = map(int, tstr.split(":"))
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables
start_location = "The Castro"
start_time_str = "9:00"

travel_times = {
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Financial District"): 20,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Financial District"): 17,
    ("Financial District", "The Castro"): 23,
    ("Financial District", "Mission District"): 17,
}

friends = {
    "Laura": {
        "location": "Mission District",
        "available_start": "12:15",
        "available_end": "19:45",
        "min_minutes": 75,
    },
    "Anthony": {
        "location": "Financial District",
        "available_start": "12:30",
        "available_end": "14:45",
        "min_minutes": 30,
    },
}

# Helpers
def schedule_for_order(order, start_loc, start_time):
    time = start_time
    loc = start_loc
    meetings = []
    total_travel = 0

    for person in order:
        info = friends[person]
        target_loc = info["location"]
        # Travel time
        if loc == target_loc:
            t_travel = 0
        else:
            t_travel = travel_times.get((loc, target_loc))
            if t_travel is None:
                return None  # No known route
        total_travel += t_travel
        arrival = time + t_travel

        avail_start = parse_time(info["available_start"])
        avail_end = parse_time(info["available_end"])
        duration = info["min_minutes"]

        start_meet = max(arrival, avail_start)
        end_meet = start_meet + duration

        if end_meet > avail_end:
            return None  # Infeasible due to availability window

        meetings.append({
            "action": "meet",
            "location": target_loc,
            "person": person,
            "start_time": fmt_time(start_meet),
            "end_time": fmt_time(end_meet),
        })

        # Update state
        time = end_meet
        loc = target_loc

    return {
        "meetings": meetings,
        "finish_time": time,
        "total_travel": total_travel,
    }

# Compute best schedule
start_time = parse_time(start_time_str)
friend_list = list(friends.keys())

best_result = None

# Try to meet as many friends as possible: test larger subsets first
for r in range(len(friend_list), 0, -1):
    candidates = []
    for order in permutations(friend_list, r):
        res = schedule_for_order(order, start_location, start_time)
        if res is not None:
            candidates.append((order, res))
    if candidates:
        # Choose the best by earliest finish time, then minimum total travel
        order, res = min(candidates, key=lambda x: (x[1]["finish_time"], x[1]["total_travel"]))
        best_result = res
        break

# Prepare output
output = {"itinerary": []}
if best_result:
    output["itinerary"] = best_result["meetings"]

print(json.dumps(output))