# SOLUTION:
import itertools
import json

def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Input variables
start_location = "Golden Gate Park"
start_time_str = "9:00"

people = [
    {"name": "Joseph", "location": "Fisherman's Wharf", "start": "8:00", "end": "17:30", "min_duration": 90},
    {"name": "Jeffrey", "location": "Bayview", "start": "17:30", "end": "21:30", "min_duration": 60},
    {"name": "Kevin", "location": "Mission District", "start": "11:15", "end": "15:15", "min_duration": 30},
    {"name": "David", "location": "Embarcadero", "start": "8:15", "end": "9:00", "min_duration": 30},
    {"name": "Barbara", "location": "Financial District", "start": "10:30", "end": "16:30", "min_duration": 15},
]

# Convert time strings to minutes
for p in people:
    p["start_min"] = time_to_minutes(p["start"])
    p["end_min"] = time_to_minutes(p["end"])

start_time = time_to_minutes(start_time_str)

# Directed travel times (in minutes)
travel = {
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Financial District"): 26,

    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Financial District"): 11,

    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Financial District"): 19,

    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Financial District"): 17,

    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Financial District"): 5,

    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Embarcadero"): 4,
}

# Add zero travel for same location
locations = {
    start_location,
    *(p["location"] for p in people)
}
for loc in locations:
    travel[(loc, loc)] = 0

def compute_schedule(order):
    # Build earliest schedule with minimum durations
    current_loc = start_location
    current_time = start_time
    entries = []
    total_travel = 0

    for p in order:
        t = travel[(current_loc, p["location"])]
        total_travel += t
        arrival = current_time + t
        start = max(arrival, p["start_min"])
        end = start + p["min_duration"]
        if end > p["end_min"]:
            return None  # infeasible
        entries.append({
            "person": p["name"],
            "location": p["location"],
            "window_start": p["start_min"],
            "window_end": p["end_min"],
            "start": start,
            "end": end,
            "min_duration": p["min_duration"]
        })
        current_loc = p["location"]
        current_time = end

    # Adjust to reduce waiting by extending meetings where possible (greedy local adjustment)
    for i in range(len(entries) - 1):
        a = entries[i]
        b = entries[i + 1]
        t = travel[(a["location"], b["location"])]
        arrival_to_b = a["end"] + t
        start_b = max(arrival_to_b, b["window_start"])  # already assigned in earliest schedule
        waiting = start_b - arrival_to_b  # >= 0
        # Extend meeting a to consume waiting, bounded by a's window
        slack_a = a["window_end"] - a["end"]
        extend = min(waiting, slack_a)
        if extend > 0:
            a["end"] += extend
            # No need to shift b's start/end because arrival now equals start_b (or still earlier than window)
            # We keep b's scheduled start as earliest feasible computed earlier.

    # Compute metrics: idle (waiting not including travel), end time
    current_loc = start_location
    current_time = start_time
    idle = 0
    total_meeting_time = 0
    for e in entries:
        t = travel[(current_loc, e["location"])]
        total_travel += 0  # already counted above per leg, but we can recompute differently if needed
        arrival = current_time + t
        if e["start"] > arrival:
            idle += e["start"] - arrival
        # Update
        total_meeting_time += e["end"] - e["start"]
        current_loc = e["location"]
        current_time = e["end"]

    end_time = entries[-1]["end"] if entries else start_time

    return {
        "entries": entries,
        "num_met": len(entries),
        "idle": idle,
        "end_time": end_time,
        "total_travel": sum(travel[(entries[i-1]["location"] if i>0 else start_location, entries[i]["location"])] for i in range(len(entries))) if entries else 0,
        "total_meeting_time": total_meeting_time
    }

# Explore all subsets and permutations
best = None

# We prioritize: max num_met, min idle, min total_travel, min end_time
def better(a, b):
    if b is None:
        return True
    if a["num_met"] != b["num_met"]:
        return a["num_met"] > b["num_met"]
    if a["idle"] != b["idle"]:
        return a["idle"] < b["idle"]
    if a["total_travel"] != b["total_travel"]:
        return a["total_travel"] < b["total_travel"]
    return a["end_time"] < b["end_time"]

for r in range(1, len(people) + 1):
    for subset in itertools.combinations(people, r):
        for perm in itertools.permutations(subset):
            sched = compute_schedule(list(perm))
            if sched is None:
                continue
            if better(sched, best):
                best = sched

# Build JSON itinerary
itinerary = []
if best:
    for e in best["entries"]:
        itinerary.append({
            "action": "meet",
            "location": e["location"],
            "person": e["person"],
            "start_time": minutes_to_time(e["start"]),
            "end_time": minutes_to_time(e["end"])
        })

output = {"itinerary": itinerary}
print(json.dumps(output, ensure_ascii=False))