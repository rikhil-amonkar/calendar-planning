import json
import itertools

def minutes(h, m):
    return h * 60 + m

def m2str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Input variables (constraints)
arrival_location = "Embarcadero"
arrival_time = minutes(9, 0)

travel = {
    "Embarcadero": {"Financial District": 5, "Alamo Square": 19},
    "Financial District": {"Embarcadero": 4, "Alamo Square": 17},
    "Alamo Square": {"Embarcadero": 17, "Financial District": 17},
}

friends = [
    {
        "name": "Stephanie",
        "location": "Financial District",
        "window_start": minutes(8, 15),
        "window_end": minutes(11, 30),
        "min_duration": 90,
    },
    {
        "name": "John",
        "location": "Alamo Square",
        "window_start": minutes(10, 15),
        "window_end": minutes(20, 45),
        "min_duration": 30,
    },
]

# Helper: build friend lookup
friend_by_name = {f["name"]: f for f in friends}
friend_names = [f["name"] for f in friends]

def simulate_order(order):
    itinerary = []
    cur_loc = arrival_location
    cur_time = arrival_time
    for name in order:
        f = friend_by_name[name]
        # Travel
        t_travel = travel[cur_loc][f["location"]]
        arrival = cur_time + t_travel
        # If early, wait until friend is available
        start = max(arrival, f["window_start"])
        end = start + f["min_duration"]
        # Check feasibility within window
        if end > f["window_end"]:
            return None  # infeasible
        itinerary.append({
            "action": "meet",
            "location": f["location"],
            "person": f["name"],
            "start_time": m2str(start),
            "end_time": m2str(end),
        })
        cur_loc = f["location"]
        cur_time = end
    return {
        "itinerary": itinerary,
        "finish_time": cur_time,
        "met_count": len(order),
        "total_meeting": sum(friend_by_name[n]["min_duration"] for n in order)
    }

# Explore schedules: all permutations of all non-empty subsets
candidates = []
n = len(friend_names)
for r in range(1, n + 1):
    for order in itertools.permutations(friend_names, r):
        res = simulate_order(order)
        if res is not None:
            candidates.append(res)

# Choose optimal: maximize number of friends met, then maximize total meeting time,
# then earliest finish time
best = None
for c in candidates:
    if best is None:
        best = c
        continue
    if c["met_count"] > best["met_count"]:
        best = c
    elif c["met_count"] == best["met_count"]:
        if c["total_meeting"] > best["total_meeting"]:
            best = c
        elif c["total_meeting"] == best["total_meeting"]:
            if c["finish_time"] < best["finish_time"]:
                best = c

# Prepare output JSON
output = {"itinerary": best["itinerary"] if best else []}
print(json.dumps(output, ensure_ascii=False))