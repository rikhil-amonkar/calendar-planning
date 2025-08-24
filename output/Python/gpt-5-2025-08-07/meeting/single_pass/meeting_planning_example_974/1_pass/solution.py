import re
import json
from copy import deepcopy

def parse_time_label(t):
    t = t.strip().upper()
    m = re.match(r"(\d{1,2}):(\d{2})(AM|PM)", t)
    if not m:
        raise ValueError(f"Invalid time: {t}")
    h = int(m.group(1))
    mi = int(m.group(2))
    ampm = m.group(3)
    if h == 12:
        h = 0
    if ampm == "PM":
        h += 12
    return h * 60 + mi

def to_hhmm(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Parse travel times from the provided data text
travel_data_text = """
Sunset District to Presidio: 16.
Sunset District to Nob Hill: 27.
Sunset District to Pacific Heights: 21.
Sunset District to Mission District: 25.
Sunset District to Marina District: 21.
Sunset District to North Beach: 28.
Sunset District to Russian Hill: 24.
Sunset District to Richmond District: 12.
Sunset District to Embarcadero: 30.
Sunset District to Alamo Square: 17.
Presidio to Sunset District: 15.
Presidio to Nob Hill: 18.
Presidio to Pacific Heights: 11.
Presidio to Mission District: 26.
Presidio to Marina District: 11.
Presidio to North Beach: 18.
Presidio to Russian Hill: 14.
Presidio to Richmond District: 7.
Presidio to Embarcadero: 20.
Presidio to Alamo Square: 19.
Nob Hill to Sunset District: 24.
Nob Hill to Presidio: 17.
Nob Hill to Pacific Heights: 8.
Nob Hill to Mission District: 13.
Nob Hill to Marina District: 11.
Nob Hill to North Beach: 8.
Nob Hill to Russian Hill: 5.
Nob Hill to Richmond District: 14.
Nob Hill to Embarcadero: 9.
Nob Hill to Alamo Square: 11.
Pacific Heights to Sunset District: 21.
Pacific Heights to Presidio: 11.
Pacific Heights to Nob Hill: 8.
Pacific Heights to Mission District: 15.
Pacific Heights to Marina District: 6.
Pacific Heights to North Beach: 9.
Pacific Heights to Russian Hill: 7.
Pacific Heights to Richmond District: 12.
Pacific Heights to Embarcadero: 10.
Pacific Heights to Alamo Square: 10.
Mission District to Sunset District: 24.
Mission District to Presidio: 25.
Mission District to Nob Hill: 12.
Mission District to Pacific Heights: 16.
Mission District to Marina District: 19.
Mission District to North Beach: 17.
Mission District to Russian Hill: 15.
Mission District to Richmond District: 20.
Mission District to Embarcadero: 19.
Mission District to Alamo Square: 11.
Marina District to Sunset District: 19.
Marina District to Presidio: 10.
Marina District to Nob Hill: 12.
Marina District to Pacific Heights: 7.
Marina District to Mission District: 20.
Marina District to North Beach: 11.
Marina District to Russian Hill: 8.
Marina District to Richmond District: 11.
Marina District to Embarcadero: 14.
Marina District to Alamo Square: 15.
North Beach to Sunset District: 27.
North Beach to Presidio: 17.
North Beach to Nob Hill: 7.
North Beach to Pacific Heights: 8.
North Beach to Mission District: 18.
North Beach to Marina District: 9.
North Beach to Russian Hill: 4.
North Beach to Richmond District: 18.
North Beach to Embarcadero: 6.
North Beach to Alamo Square: 16.
Russian Hill to Sunset District: 23.
Russian Hill to Presidio: 14.
Russian Hill to Nob Hill: 5.
Russian Hill to Pacific Heights: 7.
Russian Hill to Mission District: 16.
Russian Hill to Marina District: 7.
Russian Hill to North Beach: 5.
Russian Hill to Richmond District: 14.
Russian Hill to Embarcadero: 8.
Russian Hill to Alamo Square: 15.
Richmond District to Sunset District: 11.
Richmond District to Presidio: 7.
Richmond District to Nob Hill: 17.
Richmond District to Pacific Heights: 10.
Richmond District to Mission District: 20.
Richmond District to Marina District: 9.
Richmond District to North Beach: 17.
Richmond District to Russian Hill: 13.
Richmond District to Embarcadero: 19.
Richmond District to Alamo Square: 13.
Embarcadero to Sunset District: 30.
Embarcadero to Presidio: 20.
Embarcadero to Nob Hill: 10.
Embarcadero to Pacific Heights: 11.
Embarcadero to Mission District: 20.
Embarcadero to Marina District: 12.
Embarcadero to North Beach: 5.
Embarcadero to Russian Hill: 8.
Embarcadero to Richmond District: 21.
Embarcadero to Alamo Square: 19.
Alamo Square to Sunset District: 16.
Alamo Square to Presidio: 17.
Alamo Square to Nob Hill: 11.
Alamo Square to Pacific Heights: 10.
Alamo Square to Mission District: 10.
Alamo Square to Marina District: 15.
Alamo Square to North Beach: 15.
Alamo Square to Russian Hill: 13.
Alamo Square to Richmond District: 11.
Alamo Square to Embarcadero: 16.
""".strip()

travel = {}
pattern = re.compile(r"^(.*?) to (.*?): (\d+)\.$")
for line in travel_data_text.splitlines():
    line = line.strip()
    if not line:
        continue
    m = pattern.match(line)
    if not m:
        continue
    src = m.group(1).strip()
    dst = m.group(2).strip()
    minutes = int(m.group(3))
    if src not in travel:
        travel[src] = {}
    travel[src][dst] = minutes

# Ensure zero self-travel for known nodes
all_nodes = set(travel.keys())
for src in list(all_nodes):
    travel[src][src] = 0

def travel_time(a, b):
    if a not in travel or b not in travel[a]:
        raise KeyError(f"Missing travel time {a} -> {b}")
    return travel[a][b]

# Meeting constraints
friends = [
    {"name": "Charles", "location": "Presidio", "start": parse_time_label("1:15PM"), "end": parse_time_label("3:00PM"), "duration": 105},
    {"name": "Robert", "location": "Nob Hill", "start": parse_time_label("1:15PM"), "end": parse_time_label("5:30PM"), "duration": 90},
    {"name": "Nancy", "location": "Pacific Heights", "start": parse_time_label("2:45PM"), "end": parse_time_label("10:00PM"), "duration": 105},
    {"name": "Brian", "location": "Mission District", "start": parse_time_label("3:30PM"), "end": parse_time_label("10:00PM"), "duration": 60},
    {"name": "Kimberly", "location": "Marina District", "start": parse_time_label("5:00PM"), "end": parse_time_label("7:45PM"), "duration": 75},
    {"name": "David", "location": "North Beach", "start": parse_time_label("2:45PM"), "end": parse_time_label("4:30PM"), "duration": 75},
    {"name": "William", "location": "Russian Hill", "start": parse_time_label("12:30PM"), "end": parse_time_label("7:15PM"), "duration": 120},
    {"name": "Jeffrey", "location": "Richmond District", "start": parse_time_label("12:00PM"), "end": parse_time_label("7:15PM"), "duration": 45},
    {"name": "Karen", "location": "Embarcadero", "start": parse_time_label("2:15PM"), "end": parse_time_label("8:45PM"), "duration": 60},
    {"name": "Joshua", "location": "Alamo Square", "start": parse_time_label("6:45PM"), "end": parse_time_label("10:00PM"), "duration": 60},
]

# Start location/time
start_location = "Sunset District"
start_time = parse_time_label("9:00AM")

# Precompute latest feasible start for each friend (for quick feasibility)
for f in friends:
    f["latest_start"] = f["end"] - f["duration"]

# Helper to determine if a meeting is feasible next
def earliest_meeting_block(curr_time, curr_loc, person):
    t_travel = travel_time(curr_loc, person["location"])
    arrival = curr_time + t_travel
    start = max(arrival, person["start"])
    end = start + person["duration"]
    if end <= person["end"]:
        return start, end, t_travel
    return None

# Objective comparison: more meetings, then earlier finish, then less travel time
def is_better_solution(sol_a, sol_b):
    # sol is dict with keys: 'count', 'end_time', 'travel', 'itinerary'
    if sol_b is None:
        return True
    if sol_a["count"] != sol_b["count"]:
        return sol_a["count"] > sol_b["count"]
    if sol_a["end_time"] != sol_b["end_time"]:
        return sol_a["end_time"] < sol_b["end_time"]
    return sol_a["travel"] < sol_b["travel"]

# Backtracking search
best_solution = None

# Sort friends by earlier window end to explore urgent ones first
friends_sorted = sorted(friends, key=lambda x: x["end"])

def search(curr_time, curr_loc, remaining, itinerary, count, travel_accum):
    global best_solution
    # Upper bound pruning: even if we meet everyone remaining, cannot exceed best? skip if so
    max_possible = count + len(remaining)
    if best_solution and max_possible < best_solution["count"]:
        return

    # Try all feasible next meetings
    any_extension = False
    # Sort remaining by earlier end to prioritize urgent meetings
    remaining_sorted = sorted(remaining, key=lambda x: x["end"])
    for idx, person in enumerate(remaining_sorted):
        block = earliest_meeting_block(curr_time, curr_loc, person)
        if block is None:
            continue
        start, end, t_travel = block
        any_extension = True
        new_itinerary = itinerary + [{
            "action": "meet",
            "location": person["location"],
            "person": person["name"],
            "start_time": to_hhmm(start),
            "end_time": to_hhmm(end)
        }]
        new_remaining = remaining_sorted[:idx] + remaining_sorted[idx+1:]
        search(end, person["location"], new_remaining, new_itinerary, count + 1, travel_accum + t_travel)

    # If no further meetings can be added, evaluate the current itinerary as a candidate
    if not any_extension:
        end_time = curr_time
        candidate = {
            "count": count,
            "end_time": end_time,
            "travel": travel_accum,
            "itinerary": itinerary
        }
        if is_better_solution(candidate, best_solution):
            best_solution = candidate

# Kick off search
search(start_time, start_location, friends_sorted, [], 0, 0)

# Output best itinerary as requested JSON
output = {"itinerary": best_solution["itinerary"] if best_solution else []}
print(json.dumps(output, ensure_ascii=False))