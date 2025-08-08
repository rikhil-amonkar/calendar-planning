import itertools
import json

def hm(s):
    h, m = map(int, s.split(":"))
    return h * 60 + m

def fmt(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times in minutes between locations
travel = {
    "The Castro": {
        "Bayview": 19,
        "Pacific Heights": 16,
        "Alamo Square": 8,
        "Fisherman's Wharf": 24,
        "Golden Gate Park": 11,
    },
    "Bayview": {
        "The Castro": 20,
        "Pacific Heights": 23,
        "Alamo Square": 16,
        "Fisherman's Wharf": 25,
        "Golden Gate Park": 22,
    },
    "Pacific Heights": {
        "The Castro": 16,
        "Bayview": 22,
        "Alamo Square": 10,
        "Fisherman's Wharf": 13,
        "Golden Gate Park": 15,
    },
    "Alamo Square": {
        "The Castro": 8,
        "Bayview": 16,
        "Pacific Heights": 10,
        "Fisherman's Wharf": 19,
        "Golden Gate Park": 9,
    },
    "Fisherman's Wharf": {
        "The Castro": 26,
        "Bayview": 26,
        "Pacific Heights": 12,
        "Alamo Square": 20,
        "Golden Gate Park": 25,
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "Bayview": 23,
        "Pacific Heights": 16,
        "Alamo Square": 10,
        "Fisherman's Wharf": 24,
    },
}

start_location = "The Castro"
start_time = hm("9:00")

# Participants and constraints
min_meet = 90
friends = {
    "Rebecca": {
        "location": "Bayview",
        "start": hm("9:00"),
        "end": hm("12:45"),
        "min": min_meet,
    },
    "Amanda": {
        "location": "Pacific Heights",
        "start": hm("18:30"),
        "end": hm("21:45"),
        "min": min_meet,
    },
    "James": {
        "location": "Alamo Square",
        "start": hm("9:45"),
        "end": hm("21:15"),
        "min": min_meet,
    },
    "Sarah": {
        "location": "Fisherman's Wharf",
        "start": hm("8:00"),
        "end": hm("21:30"),
        "min": min_meet,
    },
    "Melissa": {
        "location": "Golden Gate Park",
        "start": hm("9:00"),
        "end": hm("18:45"),
        "min": min_meet,
    },
}

def build_schedule_for_order(order_names):
    itinerary = []
    cur_loc = start_location
    cur_time = start_time
    total_travel = 0
    total_wait = 0

    # To compute wait and allow stretching, we need window data quickly
    for idx, name in enumerate(order_names):
        fr = friends[name]
        loc = fr["location"]
        # Travel to this friend
        t = travel[cur_loc][loc]
        total_travel += t
        arrival = cur_time + t
        # Start at max(arrival, window start)
        start_mt = max(arrival, fr["start"])
        # Check feasibility for minimum duration
        if start_mt + fr["min"] > fr["end"]:
            return None  # infeasible
        end_mt = start_mt + fr["min"]
        # Optionally stretch to reduce waiting before next meeting (if any)
        if idx < len(order_names) - 1:
            nxt = friends[order_names[idx + 1]]
            travel_to_next = travel[loc][nxt["location"]]
            earliest_arrival_next = end_mt + travel_to_next
            if earliest_arrival_next < nxt["start"]:
                # We can extend current meeting to reduce idle wait, up to window end
                max_extension = min(nxt["start"] - earliest_arrival_next, fr["end"] - end_mt)
                if max_extension > 0:
                    end_mt += max_extension
        # Accumulate waiting time (waiting before meeting start)
        total_wait += max(0, start_mt - arrival)
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": fmt(start_mt),
            "end_time": fmt(end_mt),
        })
        cur_loc = loc
        cur_time = end_mt

    return {
        "itinerary": itinerary,
        "end_time": cur_time,
        "total_wait": total_wait,
        "total_travel": total_travel,
        "met_count": len(order_names),
    }

def better(a, b):
    # Return True if a is better than b
    # Criteria: maximize met_count, then minimize total_wait, then minimize end_time, then minimize total_travel
    if a is None:
        return False
    if b is None:
        return True
    if a["met_count"] != b["met_count"]:
        return a["met_count"] > b["met_count"]
    if a["total_wait"] != b["total_wait"]:
        return a["total_wait"] < b["total_wait"]
    if a["end_time"] != b["end_time"]:
        return a["end_time"] < b["end_time"]
    return a["total_travel"] < b["total_travel"]

names = list(friends.keys())
best = None

# Try to meet as many as possible: search subsets from largest to smallest
for k in range(len(names), 0, -1):
    best_for_k = None
    for perm in itertools.permutations(names, k):
        plan = build_schedule_for_order(perm)
        if plan is not None and better(plan, best_for_k):
            best_for_k = plan
    if best_for_k is not None:
        best = best_for_k
        break

output = {"itinerary": best["itinerary"] if best else []}
print(json.dumps(output))