import itertools
import json

# Input parameters

start_location = "Russian Hill"
start_time_str = "9:00"

# Travel times in minutes
travel_time = {
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Embarcadero"): 8,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Embarcadero"): 9,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Embarcadero"): 19,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Mission District"): 20,
}

# Friends' constraints
friends = [
    {
        "name": "Patricia",
        "location": "Nob Hill",
        "avail_start": "18:30",
        "avail_end": "21:45",
        "min_duration": 90,
    },
    {
        "name": "Ashley",
        "location": "Mission District",
        "avail_start": "20:30",
        "avail_end": "21:15",
        "min_duration": 45,
    },
    {
        "name": "Timothy",
        "location": "Embarcadero",
        "avail_start": "9:45",
        "avail_end": "17:45",
        "min_duration": 120,
    },
]

# Utility functions
def time_to_minutes(tstr):
    h, m = tstr.split(":")
    return int(h) * 60 + int(m)

def minutes_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def evaluate_order(order, start_loc, start_time_min):
    t = start_time_min
    cur_loc = start_loc
    itinerary = []
    total_wait = 0
    total_travel = 0

    for person in order:
        loc = person["location"]
        # travel time between locations
        if (cur_loc, loc) not in travel_time:
            return None  # invalid move if no travel time known
        tr = travel_time[(cur_loc, loc)]
        total_travel += tr

        earliest_arrival = t + tr
        start = max(earliest_arrival, person["avail_start_min"])
        end = start + person["min_duration"]

        if end > person["avail_end_min"]:
            return None  # cannot meet within availability

        wait = max(0, start - earliest_arrival)
        total_wait += wait

        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person["name"],
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end),
        })

        # Update for next leg
        t = end
        cur_loc = loc

    return {
        "count": len(order),
        "finish_time": t,
        "total_wait": total_wait,
        "total_travel": total_travel,
        "itinerary": itinerary,
    }

def better_plan(a, b):
    # Returns True if plan a is better than plan b
    if b is None:
        return True
    if a["count"] != b["count"]:
        return a["count"] > b["count"]
    if a["finish_time"] != b["finish_time"]:
        return a["finish_time"] < b["finish_time"]
    if a["total_wait"] != b["total_wait"]:
        return a["total_wait"] < b["total_wait"]
    return a["total_travel"] < b["total_travel"]

# Prepare data
start_time_min = time_to_minutes(start_time_str)

friends_proc = []
for f in friends:
    friends_proc.append({
        "name": f["name"],
        "location": f["location"],
        "avail_start_min": time_to_minutes(f["avail_start"]),
        "avail_end_min": time_to_minutes(f["avail_end"]),
        "min_duration": f["min_duration"],
    })

# Search for optimal plan: maximize number of friends met
best_plan = None
for k in range(len(friends_proc), 0, -1):
    for subset in itertools.combinations(friends_proc, k):
        for order in itertools.permutations(subset):
            plan = evaluate_order(order, start_location, start_time_min)
            if plan is not None and better_plan(plan, best_plan):
                best_plan = plan
    if best_plan is not None and best_plan["count"] == k:
        break  # found the best possible count for this k

# Output JSON
output = {"itinerary": best_plan["itinerary"] if best_plan else []}
print(json.dumps(output, ensure_ascii=False, separators=(",", ": ")))