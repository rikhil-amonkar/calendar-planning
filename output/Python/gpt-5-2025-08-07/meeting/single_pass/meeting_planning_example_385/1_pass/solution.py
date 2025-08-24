# SOLUTION:
import itertools
import json
import re

def parse_time_ampm(s):
    s = s.strip().upper()
    m = re.match(r'^(\d{1,2}):(\d{2})(AM|PM)$', s)
    if not m:
        raise ValueError(f"Invalid time format: {s}")
    h = int(m.group(1))
    minute = int(m.group(2))
    ap = m.group(3)
    if h == 12:
        h = 0
    if ap == 'PM':
        h += 12
    return h * 60 + minute

def minutes_to_str(m):
    h = m // 60
    minute = m % 60
    return f"{h}:{minute:02d}"

# Input variables: travel times (directed, minutes)
travel = {
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "Pacific Heights"): 8,

    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Pacific Heights"): 11,

    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Pacific Heights"): 8,

    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Pacific Heights"): 12,

    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
}

# Constraints and availability
initial_location = "Nob Hill"
initial_time = parse_time_ampm("9:00AM")

friends = [
    {
        "name": "Jeffrey",
        "location": "Presidio",
        "start": parse_time_ampm("8:00AM"),
        "end": parse_time_ampm("10:00AM"),
        "min_duration": 105,
    },
    {
        "name": "Steven",
        "location": "North Beach",
        "start": parse_time_ampm("1:30PM"),
        "end": parse_time_ampm("10:00PM"),
        "min_duration": 45,
    },
    {
        "name": "Barbara",
        "location": "Fisherman's Wharf",
        "start": parse_time_ampm("6:00PM"),
        "end": parse_time_ampm("9:30PM"),
        "min_duration": 30,
    },
    {
        "name": "John",
        "location": "Pacific Heights",
        "start": parse_time_ampm("9:00AM"),
        "end": parse_time_ampm("1:30PM"),
        "min_duration": 15,
    },
]

# Enumerate all possible schedules (subsets and orders)
best = None  # store dict with keys: itinerary, count, meet_minutes, travel_minutes, finish_time
N = len(friends)

def simulate_sequence(seq):
    current_loc = initial_location
    current_time = initial_time
    itinerary = []
    total_travel = 0
    for person in seq:
        key = (current_loc, person["location"])
        if key not in travel:
            return None  # invalid route
        t_travel = travel[key]
        total_travel += t_travel
        arrival = current_time + t_travel
        start_meet = max(arrival, person["start"])
        end_meet = start_meet + person["min_duration"]
        if end_meet > person["end"]:
            return None  # cannot meet minimum during their window
        itinerary.append({
            "action": "meet",
            "location": person["location"],
            "person": person["name"],
            "start_time": minutes_to_str(start_meet),
            "end_time": minutes_to_str(end_meet),
        })
        current_loc = person["location"]
        current_time = end_meet
    return {
        "itinerary": itinerary,
        "count": len(seq),
        "meet_minutes": sum(p["min_duration"] for p in seq),
        "travel_minutes": total_travel,
        "finish_time": current_time,
    }

# Try all subsets and permutations
for k in range(1, N + 1):
    for combo in itertools.combinations(friends, k):
        for perm in itertools.permutations(combo):
            result = simulate_sequence(perm)
            if result is None:
                continue
            # Tie-breaking: maximize count, then total meeting minutes, then minimize travel time, then earliest finish time
            key = (-result["count"], -result["meet_minutes"], result["travel_minutes"], result["finish_time"])
            if best is None or key < best["key"]:
                best = {"key": key, "plan": result}

# If no feasible meetings, output empty itinerary
output = {"itinerary": []}
if best:
    output["itinerary"] = best["plan"]["itinerary"]

print(json.dumps(output, ensure_ascii=False))