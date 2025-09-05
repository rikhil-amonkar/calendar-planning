# SOLUTION:
import json
from dataclasses import dataclass
from typing import Dict, List, Tuple

# Helper functions for time
def t(h, m=0):
    return h * 60 + m

def fmt(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times (directed, in minutes)
travel: Dict[str, Dict[str, int]] = {
    "Presidio": {
        "Fisherman's Wharf": 19,
        "Alamo Square": 19,
        "Financial District": 23,
        "Union Square": 22,
        "Sunset District": 15,
        "Embarcadero": 20,
        "Golden Gate Park": 12,
        "Chinatown": 21,
        "Richmond District": 7,
    },
    "Fisherman's Wharf": {
        "Presidio": 17,
        "Alamo Square": 21,
        "Financial District": 11,
        "Union Square": 13,
        "Sunset District": 27,
        "Embarcadero": 8,
        "Golden Gate Park": 25,
        "Chinatown": 12,
        "Richmond District": 18,
    },
    "Alamo Square": {
        "Presidio": 17,
        "Fisherman's Wharf": 19,
        "Financial District": 17,
        "Union Square": 14,
        "Sunset District": 16,
        "Embarcadero": 16,
        "Golden Gate Park": 9,
        "Chinatown": 15,
        "Richmond District": 11,
    },
    "Financial District": {
        "Presidio": 22,
        "Fisherman's Wharf": 10,
        "Alamo Square": 17,
        "Union Square": 9,
        "Sunset District": 30,
        "Embarcadero": 4,
        "Golden Gate Park": 23,
        "Chinatown": 5,
        "Richmond District": 21,
    },
    "Union Square": {
        "Presidio": 24,
        "Fisherman's Wharf": 15,
        "Alamo Square": 15,
        "Financial District": 9,
        "Sunset District": 27,
        "Embarcadero": 11,
        "Golden Gate Park": 22,
        "Chinatown": 7,
        "Richmond District": 20,
    },
    "Sunset District": {
        "Presidio": 16,
        "Fisherman's Wharf": 29,
        "Alamo Square": 17,
        "Financial District": 30,
        "Union Square": 30,
        "Embarcadero": 30,
        "Golden Gate Park": 11,
        "Chinatown": 30,
        "Richmond District": 12,
    },
    "Embarcadero": {
        "Presidio": 20,
        "Fisherman's Wharf": 6,
        "Alamo Square": 19,
        "Financial District": 5,
        "Union Square": 10,
        "Sunset District": 30,
        "Golden Gate Park": 25,
        "Chinatown": 7,
        "Richmond District": 21,
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Fisherman's Wharf": 24,
        "Alamo Square": 9,
        "Financial District": 26,
        "Union Square": 22,
        "Sunset District": 10,
        "Embarcadero": 25,
        "Chinatown": 23,
        "Richmond District": 7,
    },
    "Chinatown": {
        "Presidio": 19,
        "Fisherman's Wharf": 8,
        "Alamo Square": 17,
        "Financial District": 5,
        "Union Square": 7,
        "Sunset District": 29,
        "Embarcadero": 5,
        "Golden Gate Park": 23,
        "Richmond District": 20,
    },
    "Richmond District": {
        "Presidio": 7,
        "Fisherman's Wharf": 18,
        "Alamo Square": 13,
        "Financial District": 22,
        "Union Square": 21,
        "Sunset District": 11,
        "Embarcadero": 19,
        "Golden Gate Park": 9,
        "Chinatown": 20,
    },
}

@dataclass(frozen=True)
class Friend:
    name: str
    location: str
    start: int
    end: int
    min_duration: int

# Meeting constraints
friends: List[Friend] = [
    Friend("Jeffrey", "Fisherman's Wharf", t(10, 15), t(13, 0), 90),
    Friend("Ronald", "Alamo Square", t(7, 45), t(14, 45), 120),
    Friend("Jason", "Financial District", t(10, 45), t(16, 0), 105),
    Friend("Melissa", "Union Square", t(17, 45), t(18, 15), 15),
    Friend("Elizabeth", "Sunset District", t(14, 45), t(17, 30), 105),
    Friend("Margaret", "Embarcadero", t(13, 15), t(19, 0), 90),
    Friend("George", "Golden Gate Park", t(19, 0), t(22, 0), 75),
    Friend("Richard", "Chinatown", t(9, 30), t(21, 0), 15),
    Friend("Laura", "Richmond District", t(9, 45), t(18, 0), 60),
]

start_location = "Presidio"
start_time = t(9, 0)

# DFS search to maximize number of friends met
from functools import lru_cache

N = len(friends)

# Precompute adjacency travel for quick lookup
def get_travel(a: str, b: str) -> int:
    return travel[a][b]

# We'll use memoization on (loc, time, visited_mask) to store best result from that state
# The result includes (score tuple, itinerary list, total_travel, total_wait, finish_time)
@lru_cache(maxsize=None)
def search(current_loc: str, current_time: int, visited_mask: int):
    best_score = (-1, float('-inf'), float('-inf'), float('-inf'), "")  # (count, -finish_time, -wait, -travel, key)
    best_plan: List[Tuple[str, str, int, int]] = []  # (person, location, start, end)
    best_travel = 0
    best_wait = 0
    best_finish = current_time

    # Try each unvisited friend
    for i, fr in enumerate(friends):
        if (visited_mask >> i) & 1:
            continue
        travel_minutes = get_travel(current_loc, fr.location)
        arrival = current_time + travel_minutes
        start_mt = max(arrival, fr.start)
        end_mt = start_mt + fr.min_duration
        if end_mt > fr.end:
            continue  # infeasible

        wait_time = max(0, fr.start - arrival)

        # Recurse
        sub_score, sub_plan, sub_travel, sub_wait, sub_finish = search(fr.location, end_mt, visited_mask | (1 << i))

        # Build new stats
        total_travel = sub_travel + travel_minutes
        total_wait = sub_wait + wait_time
        finish_time = max(sub_finish, end_mt)

        # Score tuple: maximize count, minimize finish time, minimize wait, minimize travel
        count_meetings = 1 + sub_score[0] if sub_score != (-1, float('-inf'), float('-inf'), float('-inf'), "") else 1
        finish_component = -finish_time
        wait_component = -total_wait
        travel_component = -total_travel

        # Tiebreaker stable key (names sequence) to ensure determinism
        current_key = ",".join([fr.name] + [p[0] for p in sub_plan])

        score = (count_meetings, finish_component, wait_component, travel_component, current_key)

        if score > best_score:
            best_score = score
            best_plan = [(fr.name, fr.location, start_mt, end_mt)] + sub_plan
            best_travel = total_travel
            best_wait = total_wait
            best_finish = finish_time

    # Also consider the option of stopping here (no more meetings)
    if best_score[0] == -1:
        # No feasible next meetings: return zero meetings
        best_score = (0, -current_time, 0, 0, "")
        best_plan = []
        best_travel = 0
        best_wait = 0
        best_finish = current_time

    return best_score, best_plan, best_travel, best_wait, best_finish

# Run search
_, best_plan, _, _, _ = search(start_location, start_time, 0)

# Format result
itinerary = []
for person, location, s, e in best_plan:
    itinerary.append({
        "action": "meet",
        "location": location,
        "person": person,
        "start_time": fmt(s),
        "end_time": fmt(e),
    })

# Output JSON
output = {"itinerary": itinerary}
print(json.dumps(output, ensure_ascii=False))