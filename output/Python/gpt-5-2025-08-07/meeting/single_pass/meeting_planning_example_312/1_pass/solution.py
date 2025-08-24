import itertools
import json
from dataclasses import dataclass
from typing import Dict, Tuple, List, Optional

# Helper functions
def t(h: int, m: int) -> int:
    return h * 60 + m

def minutes_to_str(minutes: int) -> str:
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

# Input parameters: travel times (in minutes)
travel_minutes: Dict[Tuple[str, str], int] = {
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Golden Gate Park"): 9,

    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Golden Gate Park"): 11,

    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Golden Gate Park"): 7,

    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Golden Gate Park"): 17,

    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,
}

# Constraints
start_location = "Richmond District"
arrival_time = t(9, 0)  # 9:00

people = [
    Person(
        name="Sarah",
        location="Sunset District",
        start=t(10, 45),
        end=t(19, 0),
        min_duration=30
    ),
    Person(
        name="Richard",
        location="Haight-Ashbury",
        start=t(11, 45),
        end=t(15, 45),
        min_duration=90
    ),
    Person(
        name="Elizabeth",
        location="Mission District",
        start=t(11, 0),
        end=t(17, 15),
        min_duration=120
    ),
    Person(
        name="Michelle",
        location="Golden Gate Park",
        start=t(18, 15),
        end=t(20, 45),
        min_duration=90
    ),
]

def compute_schedule(order: List[Person]) -> Optional[dict]:
    actions = []
    current_loc = start_location
    current_time = arrival_time
    total_travel = 0
    total_idle = 0

    for idx, p in enumerate(order):
        key = (current_loc, p.location)
        if key not in travel_minutes:
            return None  # invalid path
        travel = travel_minutes[key]
        total_travel += travel

        arrival_at_p = current_time + travel
        start_mtg = max(arrival_at_p, p.start)
        if start_mtg + p.min_duration > p.end:
            return None  # infeasible due to window
        # idle waiting (whether at origin before departure or at destination) is the gap
        idle_here = max(0, start_mtg - arrival_at_p)
        total_idle += idle_here

        end_mtg = start_mtg + p.min_duration

        actions.append({
            "action": "meet",
            "location": p.location,
            "person": p.name,
            "start_time_minutes": start_mtg,
            "end_time_minutes": end_mtg
        })

        current_loc = p.location
        current_time = end_mtg

    return {
        "actions": actions,
        "finish_time": current_time,
        "total_travel": total_travel,
        "total_idle": total_idle
    }

# Evaluate all schedules: primary maximize number of friends met,
# then minimize finish time, then minimize total travel, then minimize idle time,
# then lexicographic order of names for determinism.
best_result = None
best_score = None

# Enumerate subsets from largest to smallest
for r in range(len(people), 0, -1):
    found_in_size = False
    for subset in itertools.combinations(people, r):
        for perm in itertools.permutations(subset):
            result = compute_schedule(list(perm))
            if result is None:
                continue
            count_met = len(perm)
            finish_time = result["finish_time"]
            total_travel = result["total_travel"]
            total_idle = result["total_idle"]
            names_key = tuple(p.name for p in perm)

            score = (
                count_met,                   # maximize
                -finish_time,                # minimize finish_time
                -(-total_travel),            # minimize total_travel (keep tuple consistent)
                -(-total_idle),              # minimize idle time
                tuple(names_key)             # deterministic tie-breaker
            )

            if best_score is None or score > best_score:
                best_score = score
                best_result = {
                    "perm": perm,
                    "schedule": result
                }
                found_in_size = True
    # If we found at least one feasible schedule of this size, no need to check smaller subsets
    if found_in_size:
        break

# Build final itinerary JSON
itinerary = []
if best_result is not None:
    for act in best_result["schedule"]["actions"]:
        itinerary.append({
            "action": "meet",
            "location": act["location"],
            "person": act["person"],
            "start_time": minutes_to_str(act["start_time_minutes"]),
            "end_time": minutes_to_str(act["end_time_minutes"])
        })

output = {
    "itinerary": itinerary
}

print(json.dumps(output, ensure_ascii=False))