# SOLUTION:
import json
from itertools import permutations

def time_to_min(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times (in minutes)
travel = {
    "Fisherman's Wharf": {
        "The Castro": 26,
        "Golden Gate Park": 25,
        "Embarcadero": 8,
        "Russian Hill": 7,
        "Nob Hill": 11,
        "Alamo Square": 20,
        "North Beach": 6
    },
    "The Castro": {
        "Fisherman's Wharf": 24,
        "Golden Gate Park": 11,
        "Embarcadero": 22,
        "Russian Hill": 18,
        "Nob Hill": 16,
        "Alamo Square": 8,
        "North Beach": 20
    },
    "Golden Gate Park": {
        "Fisherman's Wharf": 24,
        "The Castro": 13,
        "Embarcadero": 25,
        "Russian Hill": 19,
        "Nob Hill": 20,
        "Alamo Square": 10,
        "North Beach": 24
    },
    "Embarcadero": {
        "Fisherman's Wharf": 6,
        "The Castro": 25,
        "Golden Gate Park": 25,
        "Russian Hill": 8,
        "Nob Hill": 10,
        "Alamo Square": 19,
        "North Beach": 5
    },
    "Russian Hill": {
        "Fisherman's Wharf": 7,
        "The Castro": 21,
        "Golden Gate Park": 21,
        "Embarcadero": 8,
        "Nob Hill": 5,
        "Alamo Square": 15,
        "North Beach": 5
    },
    "Nob Hill": {
        "Fisherman's Wharf": 11,
        "The Castro": 17,
        "Golden Gate Park": 17,
        "Embarcadero": 9,
        "Russian Hill": 5,
        "Alamo Square": 11,
        "North Beach": 8
    },
    "Alamo Square": {
        "Fisherman's Wharf": 19,
        "The Castro": 8,
        "Golden Gate Park": 9,
        "Embarcadero": 17,
        "Russian Hill": 13,
        "Nob Hill": 11,
        "North Beach": 15
    },
    "North Beach": {
        "Fisherman's Wharf": 5,
        "The Castro": 22,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Russian Hill": 4,
        "Nob Hill": 7,
        "Alamo Square": 16
    }
}

# Ensure zero self-travel
for a in list(travel.keys()):
    travel[a][a] = 0

# Meeting constraints
friends_data = [
    {"name": "Laura", "location": "The Castro", "start": "19:45", "end": "21:30", "min_minutes": 105},
    {"name": "Daniel", "location": "Golden Gate Park", "start": "21:15", "end": "21:45", "min_minutes": 15},
    {"name": "William", "location": "Embarcadero", "start": "7:00", "end": "9:00", "min_minutes": 90},
    {"name": "Karen", "location": "Russian Hill", "start": "14:30", "end": "19:45", "min_minutes": 30},
    {"name": "Stephanie", "location": "Nob Hill", "start": "7:30", "end": "9:30", "min_minutes": 45},
    {"name": "Joseph", "location": "Alamo Square", "start": "11:30", "end": "12:45", "min_minutes": 15},
    {"name": "Kimberly", "location": "North Beach", "start": "15:45", "end": "19:15", "min_minutes": 30}
]

# Convert time strings to minutes
for f in friends_data:
    f["window_start"] = time_to_min(f["start"])
    f["window_end"] = time_to_min(f["end"])

start_location = "Fisherman's Wharf"
start_time = time_to_min("9:00")

# Utility: attempt to chain meetings in a specific order, greedily using earliest feasible start time
def build_schedule(order):
    schedule = []
    total_travel = 0
    curr_loc = start_location
    curr_time = start_time

    for f in order:
        # Travel time from current location to friend's location
        t = travel[curr_loc].get(f["location"])
        if t is None:
            return None  # invalid entry
        arrival = curr_time + t
        # Start at the later of arrival and window start (wait if early)
        meet_start = max(arrival, f["window_start"])
        meet_end = meet_start + f["min_minutes"]
        if meet_end > f["window_end"]:
            return None  # cannot satisfy this meeting in order
        # Record meeting
        schedule.append({
            "action": "meet",
            "location": f["location"],
            "person": f["name"],
            "start_time": min_to_time(meet_start),
            "end_time": min_to_time(meet_end)
        })
        total_travel += t
        curr_loc = f["location"]
        curr_time = meet_end

    return schedule, total_travel

# Determine feasibility of meeting a single friend at all (from day start), used to prune obvious impossibilities
def individually_feasible(f):
    # Earliest arrival from start location at day start
    t = travel[start_location].get(f["location"], 10**9)
    arrival = start_time + t
    latest_start = f["window_end"] - f["min_minutes"]
    return arrival <= f["window_end"] and max(arrival, f["window_start"]) <= latest_start

# Filter out clearly impossible meetings to reduce search
feasible_friends = [f for f in friends_data if individually_feasible(f)]

# Explore all permutations and pick best schedule
best = {
    "count": 0,
    "total_meet": 0,
    "total_travel": float('inf'),
    "schedule": []
}

# Also consider any subset orderings: generate permutations of all feasible friends and let build_schedule reject infeasible
# To ensure subset exploration, we try all permutation lengths from N down to 1
from itertools import combinations

N = len(feasible_friends)
for r in range(N, 0, -1):
    for subset in combinations(feasible_friends, r):
        # Try all orderings of this subset
        for order in permutations(subset):
            res = build_schedule(order)
            if res is None:
                continue
            schedule, total_travel = res
            count = len(schedule)
            total_meet = sum(
                time_to_min(m["end_time"]) - time_to_min(m["start_time"]) for m in schedule
            )
            # Scoring: maximize meetings, then total meeting time, then minimize travel, then earlier finish time
            finish_time = time_to_min(schedule[-1]["end_time"]) if schedule else start_time
            better = False
            if count > best["count"]:
                better = True
            elif count == best["count"]:
                if total_meet > best["total_meet"]:
                    better = True
                elif total_meet == best["total_meet"]:
                    if total_travel < best["total_travel"]:
                        better = True
                    elif total_travel == best["total_travel"]:
                        if finish_time < (time_to_min(best["schedule"][-1]["end_time"]) if best["schedule"] else start_time):
                            better = True
            if better:
                best = {
                    "count": count,
                    "total_meet": total_meet,
                    "total_travel": total_travel,
                    "schedule": schedule
                }

# Output result as JSON
output = {"itinerary": best["schedule"]}
print(json.dumps(output, ensure_ascii=False))