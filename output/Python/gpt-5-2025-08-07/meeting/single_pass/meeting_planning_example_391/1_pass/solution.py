import itertools
import json

# ----------------------------
# Helper functions for time
# ----------------------------
def time_to_minutes(tstr):
    # tstr example: '9:00', '13:30'
    h, m = tstr.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time(m):
    h = m // 60
    mins = m % 60
    return f"{h}:{mins:02d}"

# ----------------------------
# Input parameters
# ----------------------------
start_location = "Sunset District"
start_time_str = "9:00"

# Travel times (minutes) - directed
travel = {
    "Sunset District": {
        "Alamo Square": 17,
        "Russian Hill": 24,
        "Presidio": 16,
        "Financial District": 30
    },
    "Alamo Square": {
        "Sunset District": 16,
        "Russian Hill": 13,
        "Presidio": 18,
        "Financial District": 17
    },
    "Russian Hill": {
        "Sunset District": 23,
        "Alamo Square": 15,
        "Presidio": 14,
        "Financial District": 11
    },
    "Presidio": {
        "Sunset District": 15,
        "Alamo Square": 18,
        "Russian Hill": 14,
        "Financial District": 23
    },
    "Financial District": {
        "Sunset District": 31,
        "Alamo Square": 17,
        "Russian Hill": 10,
        "Presidio": 22
    }
}

# Friends with constraints
friends = [
    {
        "name": "Kevin",
        "location": "Alamo Square",
        "window_start": "8:15",
        "window_end": "21:30",
        "min_duration": 75
    },
    {
        "name": "Kimberly",
        "location": "Russian Hill",
        "window_start": "8:45",
        "window_end": "12:30",
        "min_duration": 30
    },
    {
        "name": "Joseph",
        "location": "Presidio",
        "window_start": "18:30",
        "window_end": "19:15",
        "min_duration": 45
    },
    {
        "name": "Thomas",
        "location": "Financial District",
        "window_start": "19:00",
        "window_end": "21:45",
        "min_duration": 45
    }
]

# Convert times to minutes
for f in friends:
    f["win_start_min"] = time_to_minutes(f["window_start"])
    f["win_end_min"] = time_to_minutes(f["window_end"])

start_time = time_to_minutes(start_time_str)

# ----------------------------
# Scheduling function
# ----------------------------
def schedule_order(order):
    """
    Given an order (list of friend dicts), attempt to schedule
    the meetings using earliest feasible start times.
    Returns (itinerary, finish_time, total_travel) if feasible, else None.
    """
    current_loc = start_location
    current_time = start_time
    itinerary = []
    total_travel = 0

    for f in order:
        # Travel time from current_loc to f["location"]
        if current_loc not in travel or f["location"] not in travel[current_loc]:
            return None  # Invalid travel path
        t_travel = travel[current_loc][f["location"]]
        total_travel += t_travel
        arrival = current_time + t_travel
        start_meet = max(arrival, f["win_start_min"])
        end_meet = start_meet + f["min_duration"]

        # Must fully complete meeting within the friend's window
        if end_meet > f["win_end_min"]:
            return None

        itinerary.append({
            "action": "meet",
            "location": f["location"],
            "person": f["name"],
            "start_time_min": start_meet,
            "end_time_min": end_meet
        })

        current_loc = f["location"]
        current_time = end_meet

    finish_time = current_time
    return itinerary, finish_time, total_travel

# ----------------------------
# Optimization: maximize number of meetings,
# then minimize finish time, then minimize total travel.
# ----------------------------
best = None  # tuple: (num_meetings, finish_time, total_travel, itinerary)
friend_indices = list(range(len(friends)))

# Enumerate all subsets (by size descending) and permutations
for r in range(len(friends), 0, -1):
    found_for_r = []
    for subset in itertools.combinations(friend_indices, r):
        subset_friends = [friends[i] for i in subset]
        for perm in itertools.permutations(subset_friends):
            res = schedule_order(perm)
            if res is None:
                continue
            itinerary, finish_time, total_travel = res
            found_for_r.append((r, finish_time, total_travel, itinerary))
    if found_for_r:
        # Choose best by finish_time then total_travel
        found_for_r.sort(key=lambda x: (x[1], x[2]))
        best = found_for_r[0]
        break

# If no meeting is possible (shouldn't happen), output empty itinerary
output = {"itinerary": []}

if best:
    _, _, _, itinerary = best
    output["itinerary"] = [
        {
            "action": item["action"],
            "location": item["location"],
            "person": item["person"],
            "start_time": minutes_to_time(item["start_time_min"]),
            "end_time": minutes_to_time(item["end_time_min"])
        }
        for item in itinerary
    ]

print(json.dumps(output, ensure_ascii=False))