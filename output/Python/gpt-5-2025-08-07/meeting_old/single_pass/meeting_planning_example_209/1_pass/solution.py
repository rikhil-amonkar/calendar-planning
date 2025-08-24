import itertools
import json

# Input variables
start_location = "Sunset District"
start_time_str = "9:00"

friends = [
    {
        "name": "Anthony",
        "location": "Chinatown",
        "avail_start": "13:15",
        "avail_end": "14:30",
        "min_dur": 60
    },
    {
        "name": "Rebecca",
        "location": "Russian Hill",
        "avail_start": "19:30",
        "avail_end": "21:15",
        "min_dur": 105
    },
    {
        "name": "Melissa",
        "location": "North Beach",
        "avail_start": "8:15",
        "avail_end": "13:30",
        "min_dur": 105
    }
]

# Travel times (minutes), direction-specific
travel_times = {
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "North Beach"): 29,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "North Beach"): 3,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "North Beach"): 5,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Russian Hill"): 4
}

# Utility functions
def parse_time(t):
    h, m = t.split(":")
    return int(h) * 60 + int(m)

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def travel_time(src, dst):
    if src == dst:
        return 0
    return travel_times[(src, dst)]

# Convert friend times
for f in friends:
    f["avail_start_min"] = parse_time(f["avail_start"])
    f["avail_end_min"] = parse_time(f["avail_end"])

start_time = parse_time(start_time_str)

def schedule_for_order(order):
    itinerary = []
    current_loc = start_location
    current_time = start_time
    total_meeting_minutes = 0
    total_wait_minutes = 0

    for i, friend in enumerate(order):
        # Travel to friend's location
        ttime = travel_time(current_loc, friend["location"])
        arrival = current_time + ttime
        # Start at max(arrival, availability start)
        start = max(arrival, friend["avail_start_min"])
        # If we arrive after the latest feasible start (end - min_dur), infeasible
        latest_start = friend["avail_end_min"] - friend["min_dur"]
        if start > latest_start:
            return None  # infeasible

        # Compute end time; try to maximize meeting duration but keep next feasible
        if i < len(order) - 1:
            nxt = order[i + 1]
            next_latest_start = nxt["avail_end_min"] - nxt["min_dur"]
            # Need to depart in time to reach next_latest_start
            max_end_due_to_next = next_latest_start - travel_time(friend["location"], nxt["location"])
            end_cap = min(friend["avail_end_min"], max_end_due_to_next)
        else:
            # Last friend: can go until their availability end
            end_cap = friend["avail_end_min"]

        # Ensure at least min duration
        end = max(start + friend["min_dur"], start)  # at least min_dur
        end = min(end_cap, friend["avail_end_min"])

        # If end still doesn't satisfy min duration, infeasible
        if end - start < friend["min_dur"]:
            # Try to shift start earlier if possible (arrive was already earliest)
            # No room to expand; infeasible
            return None

        # Record waiting time
        wait = max(0, start - arrival)
        total_wait_minutes += wait

        # Record meeting
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": fmt_time(start),
            "end_time": fmt_time(end)
        })
        total_meeting_minutes += (end - start)

        # Advance
        current_loc = friend["location"]
        current_time = end

    return {
        "itinerary": itinerary,
        "total_meeting_minutes": total_meeting_minutes,
        "total_wait_minutes": total_wait_minutes,
        "met_count": len(order)
    }

# Search over subsets and permutations to maximize number of friends met, then total meeting time, then minimize waiting
best = None

# Generate all subsets of friends, prioritizing larger sets
n = len(friends)
indices = list(range(n))
for r in range(n, 0, -1):
    found_for_r = False
    for combo in itertools.combinations(indices, r):
        subset = [friends[i] for i in combo]
        for perm in itertools.permutations(subset):
            result = schedule_for_order(list(perm))
            if result is None:
                continue
            if best is None:
                best = result
                found_for_r = True
            else:
                # Compare
                if (result["met_count"] > best["met_count"] or
                    (result["met_count"] == best["met_count"] and result["total_meeting_minutes"] > best["total_meeting_minutes"]) or
                    (result["met_count"] == best["met_count"] and result["total_meeting_minutes"] == best["total_meeting_minutes"] and result["total_wait_minutes"] < best["total_wait_minutes"])):
                    best = result
                    found_for_r = True
    if found_for_r:
        break  # we found at least one schedule with r friends; no need to check smaller r

output = {"itinerary": best["itinerary"] if best else []}
print(json.dumps(output, ensure_ascii=False))