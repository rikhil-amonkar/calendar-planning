# SOLUTION:
import json
from itertools import permutations

def parse_time(t):
    h, m = t.split(":")
    return int(h) * 60 + int(m)

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times (minutes) as directed edges
travel = {
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Nob Hill"): 7,

    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Nob Hill"): 8,

    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Mission District"): 18,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Nob Hill"): 8,

    ("Union Square", "North Beach"): 10,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Nob Hill"): 9,

    ("Mission District", "North Beach"): 17,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Nob Hill"): 12,

    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Nob Hill"): 20,

    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Golden Gate Park"): 17,
}

# Meeting constraints
friends = [
    {
        "name": "James",
        "location": "Pacific Heights",
        "start": parse_time("20:00"),
        "end": parse_time("22:00"),
        "min_duration": 120,
    },
    {
        "name": "Robert",
        "location": "Chinatown",
        "start": parse_time("12:15"),
        "end": parse_time("16:45"),
        "min_duration": 90,
    },
    {
        "name": "Jeffrey",
        "location": "Union Square",
        "start": parse_time("9:30"),
        "end": parse_time("15:30"),
        "min_duration": 120,
    },
    {
        "name": "Carol",
        "location": "Mission District",
        "start": parse_time("18:15"),
        "end": parse_time("21:15"),
        "min_duration": 15,
    },
    {
        "name": "Mark",
        "location": "Golden Gate Park",
        "start": parse_time("11:30"),
        "end": parse_time("17:45"),
        "min_duration": 15,
    },
    {
        "name": "Sandra",
        "location": "Nob Hill",
        "start": parse_time("8:00"),
        "end": parse_time("15:30"),
        "min_duration": 15,
    },
]

start_location = "North Beach"
start_time = parse_time("9:00")

# Utility to get travel time
def get_travel(a, b):
    return travel[(a, b)]

def schedule_from_order(order):
    # Build a schedule by greedily scheduling each friend in given order at the earliest feasible time
    loc = start_location
    t = start_time
    itinerary = []
    total_travel = 0
    total_wait = 0
    met = 0

    for f in order:
        tt = get_travel(loc, f["location"])
        arrive = t + tt
        start = max(arrive, f["start"])
        end = start + f["min_duration"]
        if end <= f["end"]:
            wait = max(0, start - arrive)
            itinerary.append({
                "action": "meet",
                "location": f["location"],
                "person": f["name"],
                "start_time": start,
                "end_time": end
            })
            met += 1
            total_travel += tt
            total_wait += wait
            t = end
            loc = f["location"]
        else:
            # not feasible in this order; skip
            continue

    return {
        "count": met,
        "travel": total_travel,
        "wait": total_wait,
        "end_time": t if itinerary else start_time,
        "itinerary": itinerary
    }

# Explore all subsets and permutations; prefer max count, then min travel, then min wait, then earliest end time
best = None

# Generate all subsets by using permutations of all friends but allowing partial prefixes:
# To consider all subsets and orders efficiently, we'll iterate over all permutations and then, for each permutation,
# build the greedy earliest-feasible schedule in that full order; this implicitly considers all ordered subsets.
from itertools import permutations

for perm in permutations(friends, len(friends)):
    result = schedule_from_order(perm)
    if best is None:
        best = result
    else:
        # Comparator: maximize count; then minimize travel; then minimize wait; then minimize end time
        if (result["count"] > best["count"] or
            (result["count"] == best["count"] and result["travel"] < best["travel"]) or
            (result["count"] == best["count"] and result["travel"] == best["travel"] and result["wait"] < best["wait"]) or
            (result["count"] == best["count"] and result["travel"] == best["travel"] and result["wait"] == best["wait"] and result["end_time"] < best["end_time"])):
            best = result

# Convert times for JSON output
json_itinerary = []
for item in best["itinerary"]:
    json_itinerary.append({
        "action": "meet",
        "location": item["location"],
        "person": item["person"],
        "start_time": fmt_time(item["start_time"]),
        "end_time": fmt_time(item["end_time"]),
    })

output = {"itinerary": json_itinerary}
print(json.dumps(output, ensure_ascii=False))