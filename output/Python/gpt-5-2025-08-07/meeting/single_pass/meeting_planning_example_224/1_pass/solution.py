# SOLUTION:
import itertools
import json

def to_minutes(t):
    # expects 24-hour 'H:MM'
    h, m = t.split(':')
    return int(h) * 60 + int(m)

def fmt_time(m):
    return f"{m // 60}:{m % 60:02d}"

# Input parameters (constraints)
start_location = "Fisherman's Wharf"
start_time_str = "9:00"

travel_minutes = {
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Richmond District"): 7,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Presidio"): 7,
}

friends = [
    {
        "name": "Melissa",
        "location": "Golden Gate Park",
        "window_start": "8:30",
        "window_end": "20:00",
        "min_duration": 15,
    },
    {
        "name": "Nancy",
        "location": "Presidio",
        "window_start": "19:45",
        "window_end": "22:00",
        "min_duration": 105,
    },
    {
        "name": "Emily",
        "location": "Richmond District",
        "window_start": "16:45",
        "window_end": "22:00",
        "min_duration": 120,
    },
]

# Convert time strings to minutes
start_time = to_minutes(start_time_str)
for f in friends:
    f["ws"] = to_minutes(f["window_start"])
    f["we"] = to_minutes(f["window_end"])

# Helper: compute earliest feasible schedule for a given order (minimal required durations)
def compute_schedule(order):
    current_loc = start_location
    current_time = start_time
    itinerary = []
    total_travel = 0
    total_wait = 0

    for f in order:
        key = (current_loc, f["location"])
        if key not in travel_minutes:
            return None  # no travel path supplied
        travel = travel_minutes[key]
        total_travel += travel
        arrival = current_time + travel
        start = max(arrival, f["ws"])
        wait = max(0, f["ws"] - arrival)
        total_wait += wait
        end = start + f["min_duration"]
        if end > f["we"]:
            return None  # cannot fit minimum meeting within window
        itinerary.append({
            "action": "meet",
            "location": f["location"],
            "person": f["name"],
            "start_time": fmt_time(start),
            "end_time": fmt_time(end),
            "_start_min": start,
            "_end_min": end
        })
        current_loc = f["location"]
        current_time = end

    finish_time = current_time
    return {
        "itinerary": itinerary,
        "finish": finish_time,
        "total_travel": total_travel,
        "total_wait": total_wait,
        "met_count": len(order)
    }

# Explore all subsets and permutations to maximize meetings, with tie-breakers:
# 1) maximize number of friends met
# 2) minimize finish time
# 3) minimize total waiting time
# 4) minimize total travel time
best = None
friends_list = friends[:]
n = len(friends_list)
for r in range(n, 0, -1):
    found_for_r = False
    for subset in itertools.combinations(friends_list, r):
        for perm in itertools.permutations(subset):
            res = compute_schedule(perm)
            if not res:
                continue
            # Evaluate against best
            if best is None:
                best = res
                found_for_r = True
            else:
                if res["met_count"] > best["met_count"]:
                    best = res
                    found_for_r = True
                elif res["met_count"] == best["met_count"]:
                    if res["finish"] < best["finish"]:
                        best = res
                        found_for_r = True
                    elif res["finish"] == best["finish"]:
                        if res["total_wait"] < best["total_wait"]:
                            best = res
                            found_for_r = True
                        elif res["total_wait"] == best["total_wait"]:
                            if res["total_travel"] < best["total_travel"]:
                                best = res
                                found_for_r = True
    if found_for_r:
        break  # we already found optimal count r

# Build output JSON
output = {"itinerary": []}
if best:
    # Strip auxiliary fields before output
    for item in best["itinerary"]:
        output["itinerary"].append({
            "action": item["action"],
            "location": item["location"],
            "person": item["person"],
            "start_time": item["start_time"],
            "end_time": item["end_time"],
        })

print(json.dumps(output, ensure_ascii=False))