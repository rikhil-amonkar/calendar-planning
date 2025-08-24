"SOLUTION:"
import json
from typing import List, Dict, Tuple

# Time utilities
def to_minutes(h, m):
    return h * 60 + m

def fmt(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Travel times (minutes) between locations (directed)
T: Dict[Tuple[str, str], int] = {}
def add(a, b, m):
    T[(a, b)] = m

# Locations
locs = [
    "Financial District",
    "Fisherman's Wharf",
    "Presidio",
    "Bayview",
    "Haight-Ashbury",
    "Russian Hill",
    "The Castro",
    "Marina District",
    "Richmond District",
    "Union Square",
    "Sunset District",
]

# Populate travel times from the problem statement
add("Financial District", "Fisherman's Wharf", 10)
add("Financial District", "Presidio", 22)
add("Financial District", "Bayview", 19)
add("Financial District", "Haight-Ashbury", 19)
add("Financial District", "Russian Hill", 11)
add("Financial District", "The Castro", 20)
add("Financial District", "Marina District", 15)
add("Financial District", "Richmond District", 21)
add("Financial District", "Union Square", 9)
add("Financial District", "Sunset District", 30)

add("Fisherman's Wharf", "Financial District", 11)
add("Fisherman's Wharf", "Presidio", 17)
add("Fisherman's Wharf", "Bayview", 26)
add("Fisherman's Wharf", "Haight-Ashbury", 22)
add("Fisherman's Wharf", "Russian Hill", 7)
add("Fisherman's Wharf", "The Castro", 27)
add("Fisherman's Wharf", "Marina District", 9)
add("Fisherman's Wharf", "Richmond District", 18)
add("Fisherman's Wharf", "Union Square", 13)
add("Fisherman's Wharf", "Sunset District", 27)

add("Presidio", "Financial District", 23)
add("Presidio", "Fisherman's Wharf", 19)
add("Presidio", "Bayview", 31)
add("Presidio", "Haight-Ashbury", 15)
add("Presidio", "Russian Hill", 14)
add("Presidio", "The Castro", 21)
add("Presidio", "Marina District", 11)
add("Presidio", "Richmond District", 7)
add("Presidio", "Union Square", 22)
add("Presidio", "Sunset District", 15)

add("Bayview", "Financial District", 19)
add("Bayview", "Fisherman's Wharf", 25)
add("Bayview", "Presidio", 32)
add("Bayview", "Haight-Ashbury", 19)
add("Bayview", "Russian Hill", 23)
add("Bayview", "The Castro", 19)
add("Bayview", "Marina District", 27)
add("Bayview", "Richmond District", 25)
add("Bayview", "Union Square", 18)
add("Bayview", "Sunset District", 23)

add("Haight-Ashbury", "Financial District", 21)
add("Haight-Ashbury", "Fisherman's Wharf", 23)
add("Haight-Ashbury", "Presidio", 15)
add("Haight-Ashbury", "Bayview", 18)
add("Haight-Ashbury", "Russian Hill", 17)
add("Haight-Ashbury", "The Castro", 6)
add("Haight-Ashbury", "Marina District", 17)
add("Haight-Ashbury", "Richmond District", 10)
add("Haight-Ashbury", "Union Square", 19)
add("Haight-Ashbury", "Sunset District", 15)

add("Russian Hill", "Financial District", 11)
add("Russian Hill", "Fisherman's Wharf", 7)
add("Russian Hill", "Presidio", 14)
add("Russian Hill", "Bayview", 23)
add("Russian Hill", "Haight-Ashbury", 17)
add("Russian Hill", "The Castro", 21)
add("Russian Hill", "Marina District", 7)
add("Russian Hill", "Richmond District", 14)
add("Russian Hill", "Union Square", 10)
add("Russian Hill", "Sunset District", 23)

add("The Castro", "Financial District", 21)
add("The Castro", "Fisherman's Wharf", 24)
add("The Castro", "Presidio", 20)
add("The Castro", "Bayview", 19)
add("The Castro", "Haight-Ashbury", 6)
add("The Castro", "Russian Hill", 18)
add("The Castro", "Marina District", 21)
add("The Castro", "Richmond District", 16)
add("The Castro", "Union Square", 19)
add("The Castro", "Sunset District", 17)

add("Marina District", "Financial District", 17)
add("Marina District", "Fisherman's Wharf", 10)
add("Marina District", "Presidio", 10)
add("Marina District", "Bayview", 27)
add("Marina District", "Haight-Ashbury", 16)
add("Marina District", "Russian Hill", 8)
add("Marina District", "The Castro", 22)
add("Marina District", "Richmond District", 11)
add("Marina District", "Union Square", 16)
add("Marina District", "Sunset District", 19)

add("Richmond District", "Financial District", 22)
add("Richmond District", "Fisherman's Wharf", 18)
add("Richmond District", "Presidio", 7)
add("Richmond District", "Bayview", 27)
add("Richmond District", "Haight-Ashbury", 10)
add("Richmond District", "Russian Hill", 13)
add("Richmond District", "The Castro", 16)
add("Richmond District", "Marina District", 9)
add("Richmond District", "Union Square", 21)
add("Richmond District", "Sunset District", 11)

add("Union Square", "Financial District", 9)
add("Union Square", "Fisherman's Wharf", 15)
add("Union Square", "Presidio", 24)
add("Union Square", "Bayview", 15)
add("Union Square", "Haight-Ashbury", 18)
add("Union Square", "Russian Hill", 13)
add("Union Square", "The Castro", 17)
add("Union Square", "Marina District", 18)
add("Union Square", "Richmond District", 20)
add("Union Square", "Sunset District", 27)

add("Sunset District", "Financial District", 30)
add("Sunset District", "Fisherman's Wharf", 29)
add("Sunset District", "Presidio", 16)
add("Sunset District", "Bayview", 22)
add("Sunset District", "Haight-Ashbury", 15)
add("Sunset District", "Russian Hill", 24)
add("Sunset District", "The Castro", 17)
add("Sunset District", "Marina District", 21)
add("Sunset District", "Richmond District", 12)
add("Sunset District", "Union Square", 30)

def travel_time(a: str, b: str) -> int:
    if a == b:
        return 0
    return T[(a, b)]

# Friends data
Friend = Dict[str, object]
friends: List[Friend] = [
    {"person": "Mark", "location": "Fisherman's Wharf", "start": to_minutes(8, 15), "end": to_minutes(10, 0), "min_dur": 30},
    {"person": "Stephanie", "location": "Presidio", "start": to_minutes(12, 15), "end": to_minutes(15, 0), "min_dur": 75},
    {"person": "Betty", "location": "Bayview", "start": to_minutes(7, 15), "end": to_minutes(20, 30), "min_dur": 15},
    {"person": "Lisa", "location": "Haight-Ashbury", "start": to_minutes(15, 30), "end": to_minutes(18, 30), "min_dur": 45},
    {"person": "William", "location": "Russian Hill", "start": to_minutes(18, 45), "end": to_minutes(20, 0), "min_dur": 60},
    {"person": "Brian", "location": "The Castro", "start": to_minutes(9, 15), "end": to_minutes(13, 15), "min_dur": 30},
    {"person": "Joseph", "location": "Marina District", "start": to_minutes(10, 45), "end": to_minutes(15, 0), "min_dur": 90},
    {"person": "Ashley", "location": "Richmond District", "start": to_minutes(9, 45), "end": to_minutes(11, 15), "min_dur": 45},
    {"person": "Patricia", "location": "Union Square", "start": to_minutes(16, 30), "end": to_minutes(20, 0), "min_dur": 120},
    {"person": "Karen", "location": "Sunset District", "start": to_minutes(16, 30), "end": to_minutes(22, 0), "min_dur": 105},
]

# Start state
start_loc = "Financial District"
start_time = to_minutes(9, 0)

# Pre-sort friends by earlier availability end (heuristic ordering)
order = sorted(range(len(friends)), key=lambda i: friends[i]["end"])

best_itinerary: List[Dict] = []
best_count = 0
best_end_time = float('inf')
best_travel = float('inf')

from functools import lru_cache

def dfs(current_loc: str, current_time: int, visited_mask: int, itinerary: List[Dict], travel_sum: int):
    global best_itinerary, best_count, best_end_time, best_travel

    # Update best if improved
    cnt = len(itinerary)
    if cnt > best_count or (cnt == best_count and (current_time < best_end_time or (current_time == best_end_time and travel_sum < best_travel))):
        best_itinerary = list(itinerary)
        best_count = cnt
        best_end_time = current_time
        best_travel = travel_sum

    # Potential upper bound: remaining total friends count
    remaining_possible = len(friends) - cnt
    if cnt + remaining_possible <= best_count:
        return

    # Try to extend with each unvisited friend, in order of earliest end to prune later-enders
    for idx in order:
        if (visited_mask >> idx) & 1:
            continue
        f = friends[idx]
        # Compute earliest start after travel
        t_travel = travel_time(current_loc, f["location"])
        arrival = current_time + t_travel
        start = max(arrival, f["start"])
        end = start + f["min_dur"]
        if end <= f["end"]:
            # feasible; choose minimal meeting duration at earliest possible start to maximize future options
            new_it = itinerary + [{
                "action": "meet",
                "location": f["location"],
                "person": f["person"],
                "start_time": fmt(start),
                "end_time": fmt(end),
            }]
            dfs(f["location"], end, visited_mask | (1 << idx), new_it, travel_sum + t_travel)

# Run search
dfs(start_loc, start_time, 0, [], 0)

# Output as JSON
print(json.dumps({"itinerary": best_itinerary}, ensure_ascii=False))