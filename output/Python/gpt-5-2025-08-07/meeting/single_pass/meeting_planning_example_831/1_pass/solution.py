"""
SOLUTION:
"""
import json
from dataclasses import dataclass
from typing import Dict, List, Tuple

# -------------------------
# Helper time functions
# -------------------------
def t(h: int, m: int) -> int:
    return h * 60 + m

def fmt(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# -------------------------
# Travel times (minutes)
# -------------------------
locations = [
    "Presidio",
    "Fisherman's Wharf",
    "Alamo Square",
    "Financial District",
    "Union Square",
    "Sunset District",
    "Embarcadero",
    "Golden Gate Park",
    "Chinatown",
    "Richmond District",
]

travel: Dict[str, Dict[str, int]] = {loc: {} for loc in locations}
def add(a: str, b: str, d: int):
    travel[a][b] = d

# Presidio
add("Presidio", "Fisherman's Wharf", 19)
add("Presidio", "Alamo Square", 19)
add("Presidio", "Financial District", 23)
add("Presidio", "Union Square", 22)
add("Presidio", "Sunset District", 15)
add("Presidio", "Embarcadero", 20)
add("Presidio", "Golden Gate Park", 12)
add("Presidio", "Chinatown", 21)
add("Presidio", "Richmond District", 7)

# Fisherman's Wharf
add("Fisherman's Wharf", "Presidio", 17)
add("Fisherman's Wharf", "Alamo Square", 21)
add("Fisherman's Wharf", "Financial District", 11)
add("Fisherman's Wharf", "Union Square", 13)
add("Fisherman's Wharf", "Sunset District", 27)
add("Fisherman's Wharf", "Embarcadero", 8)
add("Fisherman's Wharf", "Golden Gate Park", 25)
add("Fisherman's Wharf", "Chinatown", 12)
add("Fisherman's Wharf", "Richmond District", 18)

# Alamo Square
add("Alamo Square", "Presidio", 17)
add("Alamo Square", "Fisherman's Wharf", 19)
add("Alamo Square", "Financial District", 17)
add("Alamo Square", "Union Square", 14)
add("Alamo Square", "Sunset District", 16)
add("Alamo Square", "Embarcadero", 16)
add("Alamo Square", "Golden Gate Park", 9)
add("Alamo Square", "Chinatown", 15)
add("Alamo Square", "Richmond District", 11)

# Financial District
add("Financial District", "Presidio", 22)
add("Financial District", "Fisherman's Wharf", 10)
add("Financial District", "Alamo Square", 17)
add("Financial District", "Union Square", 9)
add("Financial District", "Sunset District", 30)
add("Financial District", "Embarcadero", 4)
add("Financial District", "Golden Gate Park", 23)
add("Financial District", "Chinatown", 5)
add("Financial District", "Richmond District", 21)

# Union Square
add("Union Square", "Presidio", 24)
add("Union Square", "Fisherman's Wharf", 15)
add("Union Square", "Alamo Square", 15)
add("Union Square", "Financial District", 9)
add("Union Square", "Sunset District", 27)
add("Union Square", "Embarcadero", 11)
add("Union Square", "Golden Gate Park", 22)
add("Union Square", "Chinatown", 7)
add("Union Square", "Richmond District", 20)

# Sunset District
add("Sunset District", "Presidio", 16)
add("Sunset District", "Fisherman's Wharf", 29)
add("Sunset District", "Alamo Square", 17)
add("Sunset District", "Financial District", 30)
add("Sunset District", "Union Square", 30)
add("Sunset District", "Embarcadero", 30)
add("Sunset District", "Golden Gate Park", 11)
add("Sunset District", "Chinatown", 30)
add("Sunset District", "Richmond District", 12)

# Embarcadero
add("Embarcadero", "Presidio", 20)
add("Embarcadero", "Fisherman's Wharf", 6)
add("Embarcadero", "Alamo Square", 19)
add("Embarcadero", "Financial District", 5)
add("Embarcadero", "Union Square", 10)
add("Embarcadero", "Sunset District", 30)
add("Embarcadero", "Golden Gate Park", 25)
add("Embarcadero", "Chinatown", 7)
add("Embarcadero", "Richmond District", 21)

# Golden Gate Park
add("Golden Gate Park", "Presidio", 11)
add("Golden Gate Park", "Fisherman's Wharf", 24)
add("Golden Gate Park", "Alamo Square", 9)
add("Golden Gate Park", "Financial District", 26)
add("Golden Gate Park", "Union Square", 22)
add("Golden Gate Park", "Sunset District", 10)
add("Golden Gate Park", "Embarcadero", 25)
add("Golden Gate Park", "Chinatown", 23)
add("Golden Gate Park", "Richmond District", 7)

# Chinatown
add("Chinatown", "Presidio", 19)
add("Chinatown", "Fisherman's Wharf", 8)
add("Chinatown", "Alamo Square", 17)
add("Chinatown", "Financial District", 5)
add("Chinatown", "Union Square", 7)
add("Chinatown", "Sunset District", 29)
add("Chinatown", "Embarcadero", 5)
add("Chinatown", "Golden Gate Park", 23)
add("Chinatown", "Richmond District", 20)

# Richmond District
add("Richmond District", "Presidio", 7)
add("Richmond District", "Fisherman's Wharf", 18)
add("Richmond District", "Alamo Square", 13)
add("Richmond District", "Financial District", 22)
add("Richmond District", "Union Square", 21)
add("Richmond District", "Sunset District", 11)
add("Richmond District", "Embarcadero", 19)
add("Richmond District", "Golden Gate Park", 9)
add("Richmond District", "Chinatown", 20)

# -------------------------
# Meeting constraints
# -------------------------
@dataclass(frozen=True)
class Person:
    name: str
    location: str
    window_start: int
    window_end: int
    min_duration: int

people: Dict[str, Person] = {
    "Jeffrey": Person("Jeffrey", "Fisherman's Wharf", t(10, 15), t(13, 0), 90),
    "Ronald": Person("Ronald", "Alamo Square", t(7, 45), t(14, 45), 120),
    "Jason": Person("Jason", "Financial District", t(10, 45), t(16, 0), 105),
    "Melissa": Person("Melissa", "Union Square", t(17, 45), t(18, 15), 15),
    "Elizabeth": Person("Elizabeth", "Sunset District", t(14, 45), t(17, 30), 105),
    "Margaret": Person("Margaret", "Embarcadero", t(13, 15), t(19, 0), 90),
    "George": Person("George", "Golden Gate Park", t(19, 0), t(22, 0), 75),
    "Richard": Person("Richard", "Chinatown", t(9, 30), t(21, 0), 15),
    "Laura": Person("Laura", "Richmond District", t(9, 45), t(18, 0), 60),
}

start_location = "Presidio"
start_time = t(9, 0)

# -------------------------
# Search for optimal itinerary
# -------------------------
PersonName = str
ItineraryEntry = Tuple[str, str, PersonName, int, int]  # (action, location, person, start, end)

# Pre-sort persons by window end time (earlier deadlines first) to guide search
person_order = sorted(people.keys(), key=lambda n: people[n].window_end)

best_itinerary: List[ItineraryEntry] = []
best_count = -1
best_finish_time = 10**9
best_total_travel = 10**9

def dfs(current_loc: str,
        current_time: int,
        remaining: List[PersonName],
        itinerary: List[ItineraryEntry],
        total_travel: int):
    global best_itinerary, best_count, best_finish_time, best_total_travel

    # Update best if current is better (number of meetings)
    if len(itinerary) > 0:
        finish_time = itinerary[-1][4]
    else:
        finish_time = current_time

    current_count = sum(1 for e in itinerary if e[0] == "meet")

    improved = False
    if current_count > best_count:
        improved = True
    elif current_count == best_count:
        # tie-breaker: earliest finish time; then minimal total travel
        if finish_time < best_finish_time:
            improved = True
        elif finish_time == best_finish_time and total_travel < best_total_travel:
            improved = True

    if improved:
        best_itinerary = list(itinerary)
        best_count = current_count
        best_finish_time = finish_time
        best_total_travel = total_travel

    # Upper bound: even if we met everyone remaining, could we surpass best?
    if current_count + len(remaining) <= best_count:
        return

    # Explore next meetings
    for name in remaining:
        p = people[name]
        if current_loc not in travel or p.location not in travel[current_loc]:
            continue  # no path known
        move = travel[current_loc][p.location]
        arrival = current_time + move
        start_meet = max(arrival, p.window_start)
        end_meet = start_meet + p.min_duration
        if end_meet <= p.window_end:
            new_remaining = [x for x in remaining if x != name]
            itinerary.append(("meet", p.location, p.name, start_meet, end_meet))
            dfs(p.location, end_meet, new_remaining, itinerary, total_travel + move)
            itinerary.pop()

# Begin search with heuristic ordering
dfs(start_location, start_time, person_order, [], 0)

# Build output JSON
output = {
    "itinerary": [
        {
            "action": action,
            "location": location,
            "person": person,
            "start_time": fmt(start),
            "end_time": fmt(end),
        }
        for (action, location, person, start, end) in best_itinerary
    ]
}

print(json.dumps(output, ensure_ascii=False, indent=2))