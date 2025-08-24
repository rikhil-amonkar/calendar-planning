import itertools
import json

def parse_time(t):
    h, m = t.split(":")
    return int(h) * 60 + int(m)

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables
start_location = "Union Square"
start_time_str = "9:00"

travel_times = {
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Sunset District"): 26,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Sunset District"): 24,
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Sunset District"): 23,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Bayview"): 22,
}

people = [
    {
        "name": "Rebecca",
        "location": "Mission District",
        "window_start": "11:30",
        "window_end": "20:15",
        "min_duration": 120,
    },
    {
        "name": "Karen",
        "location": "Bayview",
        "window_start": "12:45",
        "window_end": "15:00",
        "min_duration": 120,
    },
    {
        "name": "Carol",
        "location": "Sunset District",
        "window_start": "10:15",
        "window_end": "11:45",
        "min_duration": 30,
    },
]

# Preprocess times
for p in people:
    p["ws"] = parse_time(p["window_start"])
    p["we"] = parse_time(p["window_end"])

start_time = parse_time(start_time_str)
people_by_name = {p["name"]: p for p in people}

def travel_time(a, b):
    if a == b:
        return 0
    return travel_times.get((a, b), float("inf"))

def schedule_order(order):
    current_loc = start_location
    current_time = start_time
    itinerary = []
    total_travel = 0
    total_wait = 0

    for name in order:
        p = people_by_name[name]
        t_travel = travel_time(current_loc, p["location"])
        if t_travel == float("inf"):
            return None  # No path known
        arrival = current_time + t_travel
        wait = max(0, p["ws"] - arrival)
        start_meet = max(arrival, p["ws"])
        end_meet = start_meet + p["min_duration"]
        if end_meet > p["we"]:
            return None  # infeasible
        itinerary.append({
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time_min": start_meet,
            "end_time_min": end_meet,
        })
        total_travel += t_travel
        total_wait += wait
        current_loc = p["location"]
        current_time = end_meet

    return {
        "itinerary": itinerary,
        "finish_time": current_time,
        "total_travel": total_travel,
        "total_wait": total_wait,
        "count": len(order),
    }

# Explore all subsets and orders
best = None

names = [p["name"] for p in people]
for r in range(len(names), 0, -1):
    for order in itertools.permutations(names, r):
        sched = schedule_order(order)
        if not sched:
            continue
        if best is None:
            best = sched
        else:
            # Compare by: max meetings, min total_wait, min finish_time, min total_travel
            criteria_best = (best["count"], -best["total_wait"], -best["finish_time"], -best["total_travel"])
            criteria_new = (sched["count"], -sched["total_wait"], -sched["finish_time"], -sched["total_travel"])
            # Since we want larger count and smaller waits/finish/travel, we invert signs for the latter
            if criteria_new > criteria_best:
                best = sched
    if best and best["count"] == r:
        # Found a feasible schedule with max r; no need to consider smaller r
        break

# Format output
output_itinerary = []
if best:
    for item in best["itinerary"]:
        output_itinerary.append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": fmt_time(item["start_time_min"]),
            "end_time": fmt_time(item["end_time_min"]),
        })

result = {"itinerary": output_itinerary}

print(json.dumps(result, ensure_ascii=False))