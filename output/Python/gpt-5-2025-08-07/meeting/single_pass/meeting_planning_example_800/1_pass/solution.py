# SOLUTION:
import json
from functools import lru_cache
from dataclasses import dataclass

# Helper functions for time conversion
def to_min(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Starting point and time
start_location = "Union Square"
start_time_str = "9:00"
start_time = to_min(start_time_str)

# People, availabilities, and minimum meeting durations
@dataclass(frozen=True)
class Person:
    name: str
    location: str
    start: int
    end: int
    duration: int

people = [
    Person("Melissa", "The Castro", to_min("20:15"), to_min("21:15"), 30),
    Person("Kimberly", "North Beach", to_min("7:00"), to_min("10:30"), 15),
    Person("Joseph", "Embarcadero", to_min("15:30"), to_min("19:30"), 75),
    Person("Barbara", "Alamo Square", to_min("20:45"), to_min("21:45"), 15),
    Person("Kenneth", "Nob Hill", to_min("12:15"), to_min("17:15"), 105),
    Person("Joshua", "Presidio", to_min("16:30"), to_min("18:15"), 105),
    Person("Brian", "Fisherman's Wharf", to_min("9:30"), to_min("15:30"), 45),
    Person("Steven", "Mission District", to_min("19:30"), to_min("21:00"), 90),
    Person("Betty", "Haight-Ashbury", to_min("19:00"), to_min("20:30"), 90),
]

# Travel times (directed) in minutes
travel = {
    "Union Square": {
        "The Castro": 17, "North Beach": 10, "Embarcadero": 11, "Alamo Square": 15,
        "Nob Hill": 9, "Presidio": 24, "Fisherman's Wharf": 15, "Mission District": 14,
        "Haight-Ashbury": 18
    },
    "The Castro": {
        "Union Square": 19, "North Beach": 20, "Embarcadero": 22, "Alamo Square": 8,
        "Nob Hill": 16, "Presidio": 20, "Fisherman's Wharf": 24, "Mission District": 7,
        "Haight-Ashbury": 6
    },
    "North Beach": {
        "Union Square": 7, "The Castro": 23, "Embarcadero": 6, "Alamo Square": 16,
        "Nob Hill": 7, "Presidio": 17, "Fisherman's Wharf": 5, "Mission District": 18,
        "Haight-Ashbury": 18
    },
    "Embarcadero": {
        "Union Square": 10, "The Castro": 25, "North Beach": 5, "Alamo Square": 19,
        "Nob Hill": 10, "Presidio": 20, "Fisherman's Wharf": 6, "Mission District": 20,
        "Haight-Ashbury": 21
    },
    "Alamo Square": {
        "Union Square": 14, "The Castro": 8, "North Beach": 15, "Embarcadero": 16,
        "Nob Hill": 11, "Presidio": 17, "Fisherman's Wharf": 19, "Mission District": 10,
        "Haight-Ashbury": 5
    },
    "Nob Hill": {
        "Union Square": 7, "The Castro": 17, "North Beach": 8, "Embarcadero": 9,
        "Alamo Square": 11, "Presidio": 17, "Fisherman's Wharf": 10, "Mission District": 13,
        "Haight-Ashbury": 13
    },
    "Presidio": {
        "Union Square": 22, "The Castro": 21, "North Beach": 18, "Embarcadero": 20,
        "Alamo Square": 19, "Nob Hill": 18, "Fisherman's Wharf": 19, "Mission District": 26,
        "Haight-Ashbury": 15
    },
    "Fisherman's Wharf": {
        "Union Square": 13, "The Castro": 27, "North Beach": 6, "Embarcadero": 8,
        "Alamo Square": 21, "Nob Hill": 11, "Presidio": 17, "Mission District": 22,
        "Haight-Ashbury": 22
    },
    "Mission District": {
        "Union Square": 15, "The Castro": 7, "North Beach": 17, "Embarcadero": 19,
        "Alamo Square": 11, "Nob Hill": 12, "Presidio": 25, "Fisherman's Wharf": 22,
        "Haight-Ashbury": 12
    },
    "Haight-Ashbury": {
        "Union Square": 19, "The Castro": 6, "North Beach": 19, "Embarcadero": 20,
        "Alamo Square": 5, "Nob Hill": 15, "Presidio": 15, "Fisherman's Wharf": 23,
        "Mission District": 11
    },
}

locations = set(travel.keys())
# Ensure 0 travel time for same location
for a in list(travel.keys()):
    travel[a][a] = 0

def get_travel(a, b):
    if a == b:
        return 0
    return travel.get(a, {}).get(b, 10**9)

# Build index for people
name_to_idx = {p.name: i for i, p in enumerate(people)}
idx_to_person = {i: p for i, p in enumerate(people)}
N = len(people)

# Pre-sort people by window end to improve branching
order = sorted(range(N), key=lambda i: (people[i].end, people[i].start))

@dataclass
class Plan:
    itinerary: list  # list of tuples (name, location, start, end)
    total_travel: int
    finish_time: int

def score(plan: Plan):
    # Higher is better: number of meetings, then earlier finish, then less travel
    return (len(plan.itinerary), -plan.finish_time, -plan.total_travel)

@lru_cache(maxsize=None)
def dfs(cur_loc, cur_time, met_mask):
    best = Plan(itinerary=[], total_travel=0, finish_time=cur_time)
    best_score = score(best)

    # Bound: if all remaining cannot exceed current best + remaining count, typical cutoff not necessary here
    for i in order:
        if (met_mask >> i) & 1:
            continue
        p = idx_to_person[i]
        t_travel = get_travel(cur_loc, p.location)
        arrive = cur_time + t_travel
        # Earliest feasible start
        earliest_start = max(arrive, p.start)
        latest_start = p.end - p.duration
        if earliest_start > latest_start:
            continue  # infeasible
        start_meet = earliest_start
        end_meet = start_meet + p.duration

        # Recurse from this meeting end
        subplan = dfs(p.location, end_meet, met_mask | (1 << i))

        # Prepend this meeting and add travel
        new_itin = [(p.name, p.location, start_meet, end_meet)] + subplan.itinerary
        new_total_travel = t_travel + subplan.total_travel
        new_finish = subplan.finish_time if subplan.itinerary else end_meet

        candidate = Plan(new_itin, new_total_travel, new_finish)
        cand_score = score(candidate)
        if cand_score > best_score:
            best = candidate
            best_score = cand_score

    return best

best_plan = dfs(start_location, start_time, 0)

# Convert itinerary to requested JSON format with proper times and chronological order
# Our recursion builds itinerary in forward chronological order already, but ensure by sorting by start time
sorted_itin = sorted(best_plan.itinerary, key=lambda x: x[2])

output_itinerary = []
for name, location, start, end in sorted_itin:
    output_itinerary.append({
        "action": "meet",
        "location": location,
        "person": name,
        "start_time": to_str(start),
        "end_time": to_str(end)
    })

result = {"itinerary": output_itinerary}

print(json.dumps(result, ensure_ascii=False))