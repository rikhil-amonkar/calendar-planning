"SOLUTION:"

import itertools
import json
from dataclasses import dataclass

# Helper functions
def parse_ampm(t: str) -> int:
    t = t.strip().upper()
    if t.endswith("AM"):
        hm = t[:-2]
        am = True
    elif t.endswith("PM"):
        hm = t[:-2]
        am = False
    else:
        raise ValueError(f"Time must end with AM/PM: {t}")
    hm = hm.strip()
    if ":" in hm:
        h, m = hm.split(":")
    else:
        h, m = hm, "0"
    h = int(h)
    m = int(m)
    if am:
        if h == 12:
            h = 0
    else:
        if h != 12:
            h += 12
    return h * 60 + m

def minutes_to_str(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

@dataclass(frozen=True)
class Friend:
    name: str
    location: str
    start: int
    end: int
    min_duration: int

# Input variables
start_location = "North Beach"
arrival_time_str = "9:00AM"

travel_times = {
    "North Beach": {
        "Pacific Heights": 8,
        "Chinatown": 6,
        "Union Square": 7,
        "Mission District": 18,
        "Golden Gate Park": 22,
        "Nob Hill": 7,
    },
    "Pacific Heights": {
        "North Beach": 9,
        "Chinatown": 11,
        "Union Square": 12,
        "Mission District": 15,
        "Golden Gate Park": 15,
        "Nob Hill": 8,
    },
    "Chinatown": {
        "North Beach": 3,
        "Pacific Heights": 10,
        "Union Square": 7,
        "Mission District": 18,
        "Golden Gate Park": 23,
        "Nob Hill": 8,
    },
    "Union Square": {
        "North Beach": 10,
        "Pacific Heights": 15,
        "Chinatown": 7,
        "Mission District": 14,
        "Golden Gate Park": 22,
        "Nob Hill": 9,
    },
    "Mission District": {
        "North Beach": 17,
        "Pacific Heights": 16,
        "Chinatown": 16,
        "Union Square": 15,
        "Golden Gate Park": 17,
        "Nob Hill": 12,
    },
    "Golden Gate Park": {
        "North Beach": 24,
        "Pacific Heights": 16,
        "Chinatown": 23,
        "Union Square": 22,
        "Mission District": 17,
        "Nob Hill": 20,
    },
    "Nob Hill": {
        "North Beach": 8,
        "Pacific Heights": 8,
        "Chinatown": 6,
        "Union Square": 7,
        "Mission District": 13,
        "Golden Gate Park": 17,
    },
}

friends = [
    Friend("James", "Pacific Heights", parse_ampm("8:00PM"), parse_ampm("10:00PM"), 120),
    Friend("Robert", "Chinatown", parse_ampm("12:15PM"), parse_ampm("4:45PM"), 90),
    Friend("Jeffrey", "Union Square", parse_ampm("9:30AM"), parse_ampm("3:30PM"), 120),
    Friend("Carol", "Mission District", parse_ampm("6:15PM"), parse_ampm("9:15PM"), 15),
    Friend("Mark", "Golden Gate Park", parse_ampm("11:30AM"), parse_ampm("5:45PM"), 15),
    Friend("Sandra", "Nob Hill", parse_ampm("8:00AM"), parse_ampm("3:30PM"), 15),
]

start_time = parse_ampm(arrival_time_str)

# Validate travel matrix completeness for the given nodes
locations = {start_location} | {f.location for f in friends}
for frm in locations:
    if frm not in travel_times:
        raise ValueError(f"Missing travel times for origin: {frm}")
    missing_to = locations - set(travel_times[frm].keys()) - {frm}
    if missing_to:
        raise ValueError(f"Missing travel times from {frm} to: {sorted(missing_to)}")

def schedule_order(order):
    itinerary = []
    cur_loc = start_location
    cur_time = start_time
    total_travel = 0
    total_wait = 0

    for f in order:
        # Travel to friend's location
        travel = travel_times[cur_loc][f.location]
        arrive = cur_time + travel
        # Earliest feasible start
        start = max(arrive, f.start)
        end = start + f.min_duration
        # Check feasibility
        if end <= f.end:
            wait = max(0, start - arrive)
            itinerary.append({
                "person": f.name,
                "location": f.location,
                "start": start,
                "end": end,
                "travel_in": travel,
                "wait": wait
            })
            total_travel += travel
            total_wait += wait
            cur_loc = f.location
            cur_time = end
        else:
            # skip this friend if infeasible
            continue

    last_end = cur_time
    return itinerary, total_travel, total_wait, last_end

# Explore permutations and pick the optimal schedule
best = None
best_score = None

for order in itertools.permutations(friends):
    itin, t_travel, t_wait, last_end = schedule_order(order)
    count = len(itin)
    # Score: maximize count, then prefer earlier finish, then less waiting, then less travel.
    score = (count, -last_end, -t_wait, -t_travel)
    if (best is None) or (score > best_score):
        best = itin
        best_score = score

# Build JSON output
output_itinerary = []
for item in best:
    output_itinerary.append({
        "action": "meet",
        "location": item["location"],
        "person": item["person"],
        "start_time": minutes_to_str(item["start"]),
        "end_time": minutes_to_str(item["end"]),
    })

result = {"itinerary": output_itinerary}
print(json.dumps(result, indent=2))