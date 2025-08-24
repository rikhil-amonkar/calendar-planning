import json
from dataclasses import dataclass
from typing import Dict, List, Tuple

# Helper functions for time
def to_minutes(h, m):
    return h * 60 + m

def fmt_time(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

@dataclass
class Person:
    name: str
    location: str
    start: int
    end: int
    min_duration: int

# Build travel times matrix (in minutes)
travel: Dict[str, Dict[str, int]] = {
    "Russian Hill": {
        "Sunset District": 23, "Union Square": 10, "Nob Hill": 5, "Marina District": 7,
        "Richmond District": 14, "Financial District": 11, "Embarcadero": 8,
        "The Castro": 21, "Alamo Square": 15, "Presidio": 14, "Russian Hill": 0
    },
    "Sunset District": {
        "Russian Hill": 24, "Union Square": 30, "Nob Hill": 27, "Marina District": 21,
        "Richmond District": 12, "Financial District": 30, "Embarcadero": 30,
        "The Castro": 17, "Alamo Square": 17, "Presidio": 16, "Sunset District": 0
    },
    "Union Square": {
        "Russian Hill": 13, "Sunset District": 27, "Nob Hill": 9, "Marina District": 18,
        "Richmond District": 20, "Financial District": 9, "Embarcadero": 11,
        "The Castro": 17, "Alamo Square": 15, "Presidio": 24, "Union Square": 0
    },
    "Nob Hill": {
        "Russian Hill": 5, "Sunset District": 24, "Union Square": 7, "Marina District": 11,
        "Richmond District": 14, "Financial District": 9, "Embarcadero": 9,
        "The Castro": 17, "Alamo Square": 11, "Presidio": 17, "Nob Hill": 0
    },
    "Marina District": {
        "Russian Hill": 8, "Sunset District": 19, "Union Square": 16, "Nob Hill": 12,
        "Richmond District": 11, "Financial District": 17, "Embarcadero": 14,
        "The Castro": 22, "Alamo Square": 15, "Presidio": 10, "Marina District": 0
    },
    "Richmond District": {
        "Russian Hill": 13, "Sunset District": 11, "Union Square": 21, "Nob Hill": 17,
        "Marina District": 9, "Financial District": 22, "Embarcadero": 19,
        "The Castro": 16, "Alamo Square": 13, "Presidio": 7, "Richmond District": 0
    },
    "Financial District": {
        "Russian Hill": 11, "Sunset District": 30, "Union Square": 9, "Nob Hill": 8,
        "Marina District": 15, "Richmond District": 21, "Embarcadero": 4,
        "The Castro": 20, "Alamo Square": 17, "Presidio": 22, "Financial District": 0
    },
    "Embarcadero": {
        "Russian Hill": 8, "Sunset District": 30, "Union Square": 10, "Nob Hill": 10,
        "Marina District": 12, "Richmond District": 21, "Financial District": 5,
        "The Castro": 25, "Alamo Square": 19, "Presidio": 20, "Embarcadero": 0
    },
    "The Castro": {
        "Russian Hill": 18, "Sunset District": 17, "Union Square": 19, "Nob Hill": 16,
        "Marina District": 21, "Richmond District": 16, "Financial District": 21,
        "Embarcadero": 22, "Alamo Square": 8, "Presidio": 20, "The Castro": 0
    },
    "Alamo Square": {
        "Russian Hill": 13, "Sunset District": 16, "Union Square": 14, "Nob Hill": 11,
        "Marina District": 15, "Richmond District": 11, "Financial District": 17,
        "Embarcadero": 16, "The Castro": 8, "Presidio": 17, "Alamo Square": 0
    },
    "Presidio": {
        "Russian Hill": 14, "Sunset District": 15, "Union Square": 22, "Nob Hill": 18,
        "Marina District": 11, "Richmond District": 7, "Financial District": 23,
        "Embarcadero": 20, "The Castro": 21, "Alamo Square": 19, "Presidio": 0
    },
}

# Participants and constraints (times in 24h minutes)
participants: List[Person] = [
    Person("David", "Sunset District", to_minutes(9,15), to_minutes(22,0), 15),
    Person("Kenneth", "Union Square", to_minutes(21,15), to_minutes(21,45), 15),
    Person("Patricia", "Nob Hill", to_minutes(15,0), to_minutes(19,15), 120),
    Person("Mary", "Marina District", to_minutes(14,45), to_minutes(16,45), 45),
    Person("Charles", "Richmond District", to_minutes(17,15), to_minutes(21,0), 15),
    Person("Joshua", "Financial District", to_minutes(14,30), to_minutes(17,15), 90),
    Person("Ronald", "Embarcadero", to_minutes(18,15), to_minutes(20,45), 30),
    Person("George", "The Castro", to_minutes(14,15), to_minutes(19,0), 105),
    Person("Kimberly", "Alamo Square", to_minutes(9,0), to_minutes(14,30), 105),
    Person("William", "Presidio", to_minutes(7,0), to_minutes(12,45), 60),
]

# Start conditions
start_location = "Russian Hill"
start_time = to_minutes(9, 0)

# Objective scoring: maximize meetings, then minimize (wait + travel), then minimize finish time
def score_solution(count: int, total_wait: int, total_travel: int, finish_time: int) -> Tuple:
    return (count, -(total_wait + total_travel), -finish_time)

best_solution = {
    "score": (-1, 10**9, 10**9),
    "itinerary": [],
}

from functools import lru_cache

def search(current_loc: str, current_time: int, visited_mask: int,
           itinerary: List[Tuple[str, str, int, int]], total_wait: int, total_travel: int):
    global best_solution

    count = bin(visited_mask).count("1")
    finish_time = current_time
    current_score = score_solution(count, total_wait, total_travel, finish_time)
    if current_score > best_solution["score"]:
        best_solution["score"] = current_score
        best_solution["itinerary"] = itinerary.copy()

    # Upper bound pruning: how many more can we possibly meet from here individually
    remaining_indices = [i for i in range(len(participants)) if not (visited_mask & (1 << i))]
    feasible_remaining = 0
    for i in remaining_indices:
        p = participants[i]
        # time to travel then wait until availability and finish by window end
        travel_time = travel[current_loc][p.location]
        arrival = current_time + travel_time
        start = max(arrival, p.start)
        end = start + p.min_duration
        if end <= p.end:
            feasible_remaining += 1
    if count + feasible_remaining <= best_solution["score"][0]:
        return

    # Order candidates by earliest end time to improve pruning
    candidates = []
    for i in remaining_indices:
        p = participants[i]
        t_travel = travel[current_loc][p.location]
        arrival = current_time + t_travel
        start = max(arrival, p.start)
        end = start + p.min_duration
        if end <= p.end:
            candidates.append((end, start, t_travel, i, p))
    candidates.sort(key=lambda x: (x[0], x[1]))  # earliest finish first

    for end, start, t_travel, i, p in candidates:
        wait_time = max(0, p.start - (current_time + t_travel)) if (current_time + t_travel) < p.start else 0
        new_itinerary = itinerary + [("meet", p.location, p.name, start, end)]
        search(p.location, end, visited_mask | (1 << i), new_itinerary,
               total_wait + wait_time, total_travel + t_travel)

# Run the search
search(start_location, start_time, 0, [], 0, 0)

# Prepare JSON output
output = {"itinerary": []}
for action, location, person, start, end in best_solution["itinerary"]:
    output["itinerary"].append({
        "action": action,
        "location": location,
        "person": person,
        "start_time": fmt_time(start),
        "end_time": fmt_time(end),
    })

print(json.dumps(output, ensure_ascii=False))