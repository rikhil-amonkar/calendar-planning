import itertools
import json

# Input variables
start_location = "Bayview"
start_time_str = "9:00"

# Travel times (directed, in minutes)
travel = {
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Financial District"): 19,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Financial District"): 5,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Fisherman's Wharf"): 10,
}

# Friend constraints
friends = {
    "Betty": {
        "location": "Embarcadero",
        "start": "19:45",
        "end": "21:45",
        "min_minutes": 15,
    },
    "Karen": {
        "location": "Fisherman's Wharf",
        "start": "8:45",
        "end": "15:00",
        "min_minutes": 30,
    },
    "Anthony": {
        "location": "Financial District",
        "start": "9:15",
        "end": "21:30",
        "min_minutes": 105,
    },
}

def parse_time(tstr):
    # tstr is "H:MM" 24-hour
    h, m = tstr.split(":")
    return int(h) * 60 + int(m)

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Convert time strings to minutes
start_time = parse_time(start_time_str)
for name, info in friends.items():
    info["start_min"] = parse_time(info["start"])
    info["end_min"] = parse_time(info["end"])

people = list(friends.keys())

def travel_time(from_loc, to_loc):
    if from_loc == to_loc:
        return 0
    return travel[(from_loc, to_loc)]

def schedule_order(order):
    itinerary = []
    current_loc = start_location
    current_time = start_time
    total_travel = 0
    total_wait = 0

    for person in order:
        info = friends[person]
        loc = info["location"]
        dur = info["min_minutes"]
        # travel
        t = travel_time(current_loc, loc)
        arrive = current_time + t
        start_meet = max(arrive, info["start_min"])
        end_meet = start_meet + dur
        if end_meet > info["end_min"]:
            return None  # infeasible
        # accumulate
        total_travel += t
        total_wait += max(0, start_meet - arrive)
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person,
            "start_time": fmt_time(start_meet),
            "end_time": fmt_time(end_meet),
        })
        current_loc = loc
        current_time = end_meet

    finish_time = current_time
    return {
        "itinerary": itinerary,
        "total_travel": total_travel,
        "total_wait": total_wait,
        "finish_time": finish_time,
        "order": order,
    }

best = None
# Objective:
# 1) maximize number of friends met
# 2) minimize total travel time
# 3) minimize total waiting time
# 4) minimize finish time
# 5) deterministic tie: lexicographic order of names
for r in range(len(people), 0, -1):
    for order in itertools.permutations(people, r):
        sched = schedule_order(order)
        if sched is None:
            continue
        key = (-len(sched["itinerary"]), sched["total_travel"], sched["total_wait"], sched["finish_time"], tuple(sched["order"]))
        if best is None or key < best["key"]:
            best = {"key": key, "sched": sched}
    if best is not None and -best["key"][0] == r:
        # Found a feasible schedule with maximal number r; no need to check smaller r
        break

result = {"itinerary": []}
if best is not None:
    result["itinerary"] = best["sched"]["itinerary"]

print(json.dumps(result, ensure_ascii=False))