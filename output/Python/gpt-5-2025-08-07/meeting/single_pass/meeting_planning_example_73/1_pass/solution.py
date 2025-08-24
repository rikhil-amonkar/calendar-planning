import json
import itertools
from dataclasses import dataclass
from typing import List, Dict, Tuple, Optional

# ---------------------------
# Helpers for time conversion
# ---------------------------
def to_minutes(t: str) -> int:
    """Convert 'H:MM' (24h) to minutes since midnight."""
    h, m = t.split(":")
    return int(h) * 60 + int(m)

def to_hhmm(m: int) -> str:
    """Convert minutes since midnight to 'H:MM' without leading zero on hour."""
    h = m // 60
    mins = m % 60
    return f"{h}:{mins:02d}"

# ---------------------------
# Data structures
# ---------------------------
@dataclass
class Person:
    name: str
    location: str
    available_start: int
    available_end: int
    min_meeting_minutes: int

@dataclass
class ProblemInput:
    start_location: str
    arrival_time: int
    travel_time: Dict[Tuple[str, str], int]
    people: List[Person]

# ---------------------------
# Core scheduling logic
# ---------------------------
def travel_minutes(travel_map: Dict[Tuple[str, str], int], a: str, b: str) -> Optional[int]:
    if a == b:
        return 0
    return travel_map.get((a, b))

def simulate_schedule(order: List[Person], data: ProblemInput):
    """
    Generate all feasible schedules for a given order by exploring possible meeting durations:
    - Primary objective: maximize number of friends met (>= min duration each)
    - Secondary: maximize total meeting minutes
    - Tertiary: minimize end time (earlier finish)
    """
    # Backtracking to explore duration choices (min duration up to their availability window)
    best = {
        "count": -1,
        "total_minutes": -1,
        "end_time": float("inf"),
        "itinerary": []
    }

    def backtrack(idx: int, current_loc: str, current_time: int, itinerary: List[Dict], met_count: int, total_minutes: int):
        nonlocal best
        if idx == len(order):
            # Evaluate final schedule
            candidate = (met_count, total_minutes, current_time)
            best_candidate = (best["count"], best["total_minutes"], best["end_time"])
            if candidate > best_candidate:
                best = {
                    "count": met_count,
                    "total_minutes": total_minutes,
                    "end_time": current_time,
                    "itinerary": list(itinerary)
                }
            return

        person = order[idx]
        t_travel = travel_minutes(data.travel_time, current_loc, person.location)
        if t_travel is None:
            # No path; skip this person (cannot meet)
            backtrack(idx + 1, current_loc, current_time, itinerary, met_count, total_minutes)
            return

        arrival_at_loc = current_time + t_travel
        meeting_start = max(arrival_at_loc, person.available_start)
        latest_end = person.available_end

        # Option 1: Skip meeting this person (to explore other orders; might help if travel blocks others)
        backtrack(idx + 1, current_loc, current_time, itinerary, met_count, total_minutes)

        # Option 2: Meet if feasible
        if meeting_start + person.min_meeting_minutes <= latest_end:
            # Explore two representative duration choices:
            # - minimum required duration
            # - maximum possible duration
            possible_durations = sorted({person.min_meeting_minutes, latest_end - meeting_start})
            for dur in possible_durations:
                meet_start = meeting_start
                meet_end = meeting_start + dur
                entry = {
                    "action": "meet",
                    "location": person.location,
                    "person": person.name,
                    "start_time": to_hhmm(meet_start),
                    "end_time": to_hhmm(meet_end)
                }
                itinerary.append(entry)
                backtrack(idx + 1, person.location, meet_end, itinerary, met_count + 1, total_minutes + dur)
                itinerary.pop()

    backtrack(0, data.start_location, data.arrival_time, [], 0, 0)
    return best["itinerary"]

def compute_optimal_schedule(data: ProblemInput) -> List[Dict]:
    # Try all permutations of people to maximize the number met (and other criteria)
    best_overall = {
        "count": -1,
        "total_minutes": -1,
        "end_time": float("inf"),
        "itinerary": []
    }
    for order in itertools.permutations(data.people):
        itinerary = simulate_schedule(list(order), data)
        count = len(itinerary)
        total_minutes = 0
        end_time = data.arrival_time
        if itinerary:
            total_minutes = sum(
                to_minutes(item["end_time"]) - to_minutes(item["start_time"]) for item in itinerary
            )
            end_time = to_minutes(itinerary[-1]["end_time"])
        candidate = (count, total_minutes, -end_time)  # earlier end time preferred -> larger negative end_time
        current_best = (best_overall["count"], best_overall["total_minutes"], -best_overall["end_time"])
        if candidate > current_best:
            best_overall = {
                "count": count,
                "total_minutes": total_minutes,
                "end_time": end_time,
                "itinerary": itinerary
            }
    return best_overall["itinerary"]

# ---------------------------
# Define input parameters
# ---------------------------
def build_problem() -> ProblemInput:
    start_location = "Russian Hill"
    arrival_time = to_minutes("9:00")

    # Travel times (minutes)
    travel_time = {
        ("Russian Hill", "Pacific Heights"): 7,
        ("Pacific Heights", "Russian Hill"): 7,
    }

    # People and their constraints
    people = [
        Person(
            name="Barbara",
            location="Pacific Heights",
            available_start=to_minutes("7:15"),
            available_end=to_minutes("22:00"),
            min_meeting_minutes=60
        )
    ]

    return ProblemInput(
        start_location=start_location,
        arrival_time=arrival_time,
        travel_time=travel_time,
        people=people
    )

# ---------------------------
# Main
# ---------------------------
def main():
    data = build_problem()
    itinerary = compute_optimal_schedule(data)
    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()