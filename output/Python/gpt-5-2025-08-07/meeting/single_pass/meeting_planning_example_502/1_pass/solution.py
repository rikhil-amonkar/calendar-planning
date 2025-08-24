import json
from itertools import permutations

def parse_time(s):
    h, m = s.split(":")
    return int(h) * 60 + int(m)

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Input variables
start_location = "Financial District"
arrival_time_str = "9:00"

# Travel times (directed, in minutes)
T = {
    "Financial District": {
        "Golden Gate Park": 23, "Chinatown": 5, "Union Square": 9,
        "Fisherman's Wharf": 10, "Pacific Heights": 13, "North Beach": 7
    },
    "Golden Gate Park": {
        "Financial District": 26, "Chinatown": 23, "Union Square": 22,
        "Fisherman's Wharf": 24, "Pacific Heights": 16, "North Beach": 24
    },
    "Chinatown": {
        "Financial District": 5, "Golden Gate Park": 23, "Union Square": 7,
        "Fisherman's Wharf": 8, "Pacific Heights": 10, "North Beach": 3
    },
    "Union Square": {
        "Financial District": 9, "Golden Gate Park": 22, "Chinatown": 7,
        "Fisherman's Wharf": 15, "Pacific Heights": 15, "North Beach": 10
    },
    "Fisherman's Wharf": {
        "Financial District": 11, "Golden Gate Park": 25, "Chinatown": 12,
        "Union Square": 13, "Pacific Heights": 13, "North Beach": 6
    },
    "Pacific Heights": {
        "Financial District": 13, "Golden Gate Park": 15, "Chinatown": 11,
        "Union Square": 12, "Fisherman's Wharf": 13, "North Beach": 9
    },
    "North Beach": {
        "Financial District": 8, "Golden Gate Park": 22, "Chinatown": 6,
        "Union Square": 7, "Fisherman's Wharf": 5, "Pacific Heights": 8
    }
}

friends = [
    {"name": "Stephanie", "location": "Golden Gate Park", "start": "11:00", "end": "15:00", "min_duration": 105},
    {"name": "Karen", "location": "Chinatown", "start": "13:45", "end": "16:30", "min_duration": 15},
    {"name": "Brian", "location": "Union Square", "start": "15:00", "end": "17:15", "min_duration": 30},
    {"name": "Rebecca", "location": "Fisherman's Wharf", "start": "8:00", "end": "11:15", "min_duration": 30},
    {"name": "Joseph", "location": "Pacific Heights", "start": "8:15", "end": "9:30", "min_duration": 60},
    {"name": "Steven", "location": "North Beach", "start": "14:30", "end": "20:45", "min_duration": 120},
]

# Convert time strings to minutes for computation
for f in friends:
    f["start_min"] = parse_time(f["start"])
    f["end_min"] = parse_time(f["end"])

start_time = parse_time(arrival_time_str)

def feasible_meeting(curr_loc, curr_time, friend):
    # travel
    travel = T[curr_loc][friend["location"]]
    arrival = curr_time + travel
    start = max(arrival, friend["start_min"])
    end = start + friend["min_duration"]
    if end > friend["end_min"]:
        return None
    return {
        "start": start,
        "end": end,
        "travel": travel,
        "arrival": arrival
    }

def better_solution(a, b):
    # a and b are solution dicts with keys: itinerary, count, finish_time, travel, meeting
    # Primary: maximize count
    if a["count"] != b["count"]:
        return a["count"] > b["count"]
    # Secondary: minimize finish_time
    if a["finish_time"] != b["finish_time"]:
        return a["finish_time"] < b["finish_time"]
    # Tertiary: minimize total travel
    if a["travel"] != b["travel"]:
        return a["travel"] < b["travel"]
    # Next: maximize total meeting minutes
    if a["meeting"] != b["meeting"]:
        return a["meeting"] > b["meeting"]
    # Final tie-breaker: lexicographically smallest itinerary by times and names
    a_key = [(x["start_time"], x["end_time"], x["person"], x["location"]) for x in a["itinerary"]]
    b_key = [(x["start_time"], x["end_time"], x["person"], x["location"]) for x in b["itinerary"]]
    return a_key < b_key

best_overall = None

def search(curr_loc, curr_time, remaining, itinerary, total_travel, total_meeting):
    global best_overall
    # Current solution
    current_solution = {
        "itinerary": itinerary,
        "count": len(itinerary),
        "finish_time": curr_time,
        "travel": total_travel,
        "meeting": total_meeting
    }
    if best_overall is None or better_solution(current_solution, best_overall):
        best_overall = current_solution

    # Try to add another friend
    # Heuristic: try friends sorted by earliest latest-start (end - min_duration), then by start time
    candidates = sorted(
        remaining,
        key=lambda f: (f["end_min"] - f["min_duration"], f["start_min"])
    )
    for f in candidates:
        meet = feasible_meeting(curr_loc, curr_time, f)
        if meet is None:
            continue
        start_str = minutes_to_str(meet["start"])
        end_str = minutes_to_str(meet["end"])
        new_item = {
            "action": "meet",
            "location": f["location"],
            "person": f["name"],
            "start_time": start_str,
            "end_time": end_str
        }
        new_itin = itinerary + [new_item]
        new_remaining = [x for x in remaining if x["name"] != f["name"]]
        search(f["location"], meet["end"], new_remaining, new_itin, total_travel + meet["travel"], total_meeting + (meet["end"] - meet["start"]))

# Run the search
search(start_location, start_time, friends, [], 0, 0)

# Output result
output = {"itinerary": best_overall["itinerary"] if best_overall else []}
print(json.dumps(output, indent=2))