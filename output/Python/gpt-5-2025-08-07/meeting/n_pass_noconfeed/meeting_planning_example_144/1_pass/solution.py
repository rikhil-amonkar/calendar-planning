import json
import itertools

# Helper functions
def to_minutes(tstr):
    # tstr like '9:00' or '12:30' in 24h
    h, m = map(int, tstr.split(":"))
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables (constraints and travel times)
locations = ["The Castro", "Mission District", "Financial District"]

travel_time_min = {
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Financial District"): 20,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Financial District"): 17,
    ("Financial District", "The Castro"): 23,
    ("Financial District", "Mission District"): 17,
}

start_location = "The Castro"
arrival_time_str = "9:00"
arrival_time_min = to_minutes(arrival_time_str)

people = [
    {
        "name": "Laura",
        "location": "Mission District",
        "avail_start": to_minutes("12:15"),
        "avail_end": to_minutes("19:45"),
        "min_meet": 75
    },
    {
        "name": "Anthony",
        "location": "Financial District",
        "avail_start": to_minutes("12:30"),
        "avail_end": to_minutes("14:45"),
        "min_meet": 30
    }
]

def travel(a, b):
    if a == b:
        return 0
    return travel_time_min[(a, b)]

def schedule_two(p1, p2):
    # Start from initial conditions
    cur_loc = start_location
    cur_time = arrival_time_min

    # Go to p1
    arr1 = cur_time + travel(cur_loc, p1["location"])
    s1 = max(arr1, p1["avail_start"])
    # Feasible to start?
    if s1 > p1["avail_end"] - p1["min_meet"]:
        return None

    # Determine d1 bounds
    d1_min = p1["min_meet"]
    d1_max = p1["avail_end"] - s1

    # Must leave p1 in time to meet p2 for at least min at p2
    t12 = travel(p1["location"], p2["location"])
    # latest we can leave p1 so that arrival at p2 <= p2_end - p2_min
    leave1_latest = p2["avail_end"] - p2["min_meet"] - t12
    # thus d1 must satisfy s1 + d1 <= leave1_latest
    d1_max_eff = min(d1_max, leave1_latest - s1)

    if d1_max_eff < d1_min:
        return None

    # Choose d1 to maximize total meeting time with both.
    # Picking the largest feasible d1 reduces or eliminates waiting for p2 without reducing total sum beyond constraints.
    d1 = d1_max_eff

    e1 = s1 + d1

    # Go to p2
    arr2 = e1 + t12
    s2 = max(arr2, p2["avail_start"])
    if s2 > p2["avail_end"] - p2["min_meet"]:
        return None
    d2 = p2["avail_end"] - s2
    e2 = s2 + d2

    itinerary = [
        {"action": "meet", "location": p1["location"], "person": p1["name"], "start_time": fmt_time(s1), "end_time": fmt_time(e1)},
        {"action": "meet", "location": p2["location"], "person": p2["name"], "start_time": fmt_time(s2), "end_time": fmt_time(e2)},
    ]
    total_meeting = d1 + d2
    return {"itinerary": itinerary, "num_met": 2, "total_minutes": total_meeting, "end_time": e2}

def schedule_one(p):
    cur_loc = start_location
    cur_time = arrival_time_min
    arr = cur_time + travel(cur_loc, p["location"])
    s = max(arr, p["avail_start"])
    if s > p["avail_end"] - p["min_meet"]:
        return None
    d = p["avail_end"] - s  # maximize time with the friend
    e = s + d
    itinerary = [
        {"action": "meet", "location": p["location"], "person": p["name"], "start_time": fmt_time(s), "end_time": fmt_time(e)}
    ]
    return {"itinerary": itinerary, "num_met": 1, "total_minutes": d, "end_time": e}

# Explore schedules
candidates = []

# All permutations of two-person meetings
for p1, p2 in itertools.permutations(people, 2):
    result = schedule_two(p1, p2)
    if result:
        candidates.append(result)

# Single-person options
for p in people:
    result = schedule_one(p)
    if result:
        candidates.append(result)

# Choose optimal: maximize number of friends met, then total meeting time, then earliest end_time
def candidate_key(c):
    return (c["num_met"], c["total_minutes"], -c["end_time"] * -1)  # last transforms to prefer smaller end_time

# Explicitly sort with tie-breakers: num_met desc, total_minutes desc, end_time asc
candidates.sort(key=lambda c: (c["num_met"], c["total_minutes"], -c["end_time"]), reverse=True)
# However, reverse=True flips end_time; adjust by custom sort:
candidates = sorted(candidates, key=lambda c: (-c["num_met"], -c["total_minutes"], c["end_time"]))

best = candidates[0] if candidates else {"itinerary": []}

print(json.dumps({"itinerary": best["itinerary"]}, ensure_ascii=False))