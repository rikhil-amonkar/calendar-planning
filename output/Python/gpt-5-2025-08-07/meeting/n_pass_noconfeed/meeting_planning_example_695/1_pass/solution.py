import json
from dataclasses import dataclass
from typing import Dict, List, Tuple, Optional

# ------------------------
# Time utilities
# ------------------------
def parse_time(s: str) -> int:
    s = s.strip().upper()
    if s.endswith("AM") or s.endswith("PM"):
        ampm = s[-2:]
        t = s[:-2]
    else:
        # assume 24h format like '13:30'
        ampm = None
        t = s
    h, m = t.split(":")
    h = int(h)
    m = int(m)
    if ampm == "AM":
        if h == 12:
            h = 0
    elif ampm == "PM":
        if h != 12:
            h += 12
    return h * 60 + m

def minutes_to_time(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# ------------------------
# Data structures
# ------------------------
@dataclass(frozen=True)
class Person:
    name: str
    location: str
    start: int  # minutes from midnight
    end: int    # minutes from midnight
    min_duration: int  # minutes

# ------------------------
# Input variables (constraints)
# ------------------------
start_location = "Bayview"
start_time_str = "9:00AM"
start_time = parse_time(start_time_str)

# Travel times (directed, in minutes)
travel: Dict[str, Dict[str, int]] = {
    "Bayview": {
        "Nob Hill": 20, "Union Square": 17, "Chinatown": 18, "The Castro": 20,
        "Presidio": 31, "Pacific Heights": 23, "Russian Hill": 23
    },
    "Nob Hill": {
        "Bayview": 19, "Union Square": 7, "Chinatown": 6, "The Castro": 17,
        "Presidio": 17, "Pacific Heights": 8, "Russian Hill": 5
    },
    "Union Square": {
        "Bayview": 15, "Nob Hill": 9, "Chinatown": 7, "The Castro": 19,
        "Presidio": 24, "Pacific Heights": 15, "Russian Hill": 13
    },
    "Chinatown": {
        "Bayview": 22, "Nob Hill": 8, "Union Square": 7, "The Castro": 22,
        "Presidio": 19, "Pacific Heights": 10, "Russian Hill": 7
    },
    "The Castro": {
        "Bayview": 19, "Nob Hill": 16, "Union Square": 19, "Chinatown": 20,
        "Presidio": 20, "Pacific Heights": 16, "Russian Hill": 18
    },
    "Presidio": {
        "Bayview": 31, "Nob Hill": 18, "Union Square": 22, "Chinatown": 21,
        "The Castro": 21, "Pacific Heights": 11, "Russian Hill": 14
    },
    "Pacific Heights": {
        "Bayview": 22, "Nob Hill": 8, "Union Square": 12, "Chinatown": 11,
        "The Castro": 16, "Presidio": 11, "Russian Hill": 7
    },
    "Russian Hill": {
        "Bayview": 23, "Nob Hill": 5, "Union Square": 11, "Chinatown": 9,
        "The Castro": 21, "Presidio": 14, "Pacific Heights": 7
    },
}

# People and constraints
people: List[Person] = [
    Person("Paul", "Nob Hill", parse_time("4:15PM"), parse_time("9:15PM"), 60),
    Person("Carol", "Union Square", parse_time("6:00PM"), parse_time("8:15PM"), 120),
    Person("Patricia", "Chinatown", parse_time("8:00PM"), parse_time("9:30PM"), 75),
    Person("Karen", "The Castro", parse_time("5:00PM"), parse_time("7:00PM"), 45),
    Person("Nancy", "Presidio", parse_time("11:45AM"), parse_time("10:00PM"), 30),
    Person("Jeffrey", "Pacific Heights", parse_time("8:00PM"), parse_time("8:45PM"), 45),
    Person("Matthew", "Russian Hill", parse_time("3:45PM"), parse_time("9:45PM"), 75),
]

# ------------------------
# Search for optimal schedule
# Objective: maximize number of people met
# Tie-breakers: minimize total waiting time, then minimize total travel time, then earliest finish time
# ------------------------
from functools import lru_cache

# Ensure travel time exists
def get_travel_time(a: str, b: str) -> Optional[int]:
    if a == b:
        return 0
    return travel.get(a, {}).get(b, None)

# Sort people by earliest end to help pruning (optional heuristic)
people_sorted = sorted(people, key=lambda p: (p.end, p.start))

# Precompute index mapping
name_to_index = {p.name: i for i, p in enumerate(people_sorted)}

# DFS with memoization
@lru_cache(maxsize=None)
def dfs(current_loc: str, current_time: int, met_mask: int) -> Tuple[int, int, int, int, Tuple]:
    # Returns tuple:
    # (count_met, total_wait, total_travel, final_time, itinerary_tuple)
    best = (0, 10**9, 10**9, current_time, tuple())  # initialize with large waits/travel for tie-breaking

    # Try meeting each person not yet met
    for i, person in enumerate(people_sorted):
        if (met_mask >> i) & 1:
            continue
        tt = get_travel_time(current_loc, person.location)
        if tt is None:
            continue
        arrival = current_time + tt
        # If we arrive after their end minus min_duration, infeasible
        earliest_start = max(arrival, person.start)
        end_time = earliest_start + person.min_duration
        if end_time > person.end:
            continue  # can't meet this person
        wait_time = max(0, person.start - arrival)

        next_mask = met_mask | (1 << i)
        sub_count, sub_wait, sub_travel, sub_final, sub_itin = dfs(
            person.location, end_time, next_mask
        )
        # Include this meeting
        count = 1 + sub_count
        total_wait = wait_time + sub_wait
        total_travel = tt + sub_travel
        final_time = sub_final

        # Build itinerary entry
        meet_entry = (
            person.name,
            person.location,
            earliest_start,
            end_time
        )
        itinerary = (meet_entry,) + sub_itin

        candidate = (count, total_wait, total_travel, final_time, itinerary)

        # Compare with current best
        if candidate[0] > best[0]:
            best = candidate
        elif candidate[0] == best[0]:
            if candidate[1] < best[1]:
                best = candidate
            elif candidate[1] == best[1]:
                if candidate[2] < best[2]:
                    best = candidate
                elif candidate[2] == best[2]:
                    if candidate[3] < best[3]:
                        best = candidate

    # Also consider stopping now (no more meetings)
    # Compare zero additional meetings with current best
    stop_candidate = (0, 0, 0, current_time, tuple())
    if stop_candidate[0] > best[0]:
        best = stop_candidate
    elif stop_candidate[0] == best[0]:
        if stop_candidate[1] < best[1]:
            best = stop_candidate
        elif stop_candidate[1] == best[1]:
            if stop_candidate[2] < best[2]:
                best = stop_candidate
            elif stop_candidate[2] == best[2]:
                if stop_candidate[3] < best[3]:
                    best = stop_candidate

    return best

# Run search from starting state
result = dfs(start_location, start_time, 0)
count_met, total_wait, total_travel, final_time, itinerary_tuple = result

# Prepare JSON output
itinerary_list = []
for (person_name, location, start_min, end_min) in itinerary_tuple:
    itinerary_list.append({
        "action": "meet",
        "location": location,
        "person": person_name,
        "start_time": minutes_to_time(start_min),
        "end_time": minutes_to_time(end_min),
    })

output = {"itinerary": itinerary_list}

print(json.dumps(output))