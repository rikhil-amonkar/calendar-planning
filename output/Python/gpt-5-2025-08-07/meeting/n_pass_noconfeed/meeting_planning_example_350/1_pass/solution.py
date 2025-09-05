# SOLUTION:
import json
from itertools import permutations, combinations
from dataclasses import dataclass

# Helper functions for time handling
def to_minutes(h, m):
    return h * 60 + m

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

@dataclass
class Person:
    name: str
    location: str
    window_start: int  # minutes since midnight
    window_end: int    # minutes since midnight
    min_duration: int  # minutes

def compute_schedule(order, start_location, start_time, travel):
    current_loc = start_location
    current_time = start_time
    itinerary = []
    total_travel = 0

    for person in order:
        # Travel
        travel_time = travel[current_loc][person.location]
        total_travel += travel_time
        arrival = current_time + travel_time

        # Wait if early
        start_meet = max(arrival, person.window_start)
        end_meet = start_meet + person.min_duration

        # Check feasibility
        if end_meet > person.window_end:
            return None  # infeasible

        # Record meeting
        itinerary.append({
            "action": "meet",
            "location": person.location,
            "person": person.name,
            "start_time": minutes_to_str(start_meet),
            "end_time": minutes_to_str(end_meet)
        })

        # Update current state
        current_time = end_meet
        current_loc = person.location

    return {
        "itinerary": itinerary,
        "finish_time": current_time,
        "total_travel": total_travel
    }

def main():
    # Input variables (constraints and travel times)
    start_location = "Bayview"
    start_time = to_minutes(9, 0)  # 9:00

    friends = [
        Person(
            name="Mary",
            location="Pacific Heights",
            window_start=to_minutes(10, 0),
            window_end=to_minutes(19, 0),
            min_duration=45
        ),
        Person(
            name="Lisa",
            location="Mission District",
            window_start=to_minutes(20, 30),
            window_end=to_minutes(22, 0),
            min_duration=75
        ),
        Person(
            name="Betty",
            location="Haight-Ashbury",
            window_start=to_minutes(7, 15),
            window_end=to_minutes(17, 15),
            min_duration=90
        ),
        Person(
            name="Charles",
            location="Financial District",
            window_start=to_minutes(11, 15),
            window_end=to_minutes(15, 0),
            min_duration=120
        ),
    ]

    # Directed travel times in minutes
    travel = {
        "Bayview": {
            "Pacific Heights": 23,
            "Mission District": 13,
            "Haight-Ashbury": 19,
            "Financial District": 19,
            "Bayview": 0
        },
        "Pacific Heights": {
            "Bayview": 22,
            "Mission District": 15,
            "Haight-Ashbury": 11,
            "Financial District": 13,
            "Pacific Heights": 0
        },
        "Mission District": {
            "Bayview": 15,
            "Pacific Heights": 16,
            "Haight-Ashbury": 12,
            "Financial District": 17,
            "Mission District": 0
        },
        "Haight-Ashbury": {
            "Bayview": 18,
            "Pacific Heights": 12,
            "Mission District": 11,
            "Financial District": 21,
            "Haight-Ashbury": 0
        },
        "Financial District": {
            "Bayview": 19,
            "Pacific Heights": 13,
            "Mission District": 17,
            "Haight-Ashbury": 19,
            "Financial District": 0
        }
    }

    # Optimization: maximize number of friends met; tie-breaker: earliest finish time; then minimal total travel
    best = None
    best_count = -1

    # Try all subset sizes from largest to smallest
    n = len(friends)
    for r in range(n, 0, -1):
        feasible_found_for_r = False
        for subset in combinations(friends, r):
            for order in permutations(subset):
                result = compute_schedule(order, start_location, start_time, travel)
                if result is None:
                    continue
                feasible_found_for_r = True
                count = len(result["itinerary"])
                if count > best_count:
                    best = result
                    best_count = count
                else:
                    if count == best_count:
                        # Tie-breaker: earliest finish time
                        if result["finish_time"] < best["finish_time"]:
                            best = result
                        elif result["finish_time"] == best["finish_time"]:
                            # Next tie-breaker: minimal total travel
                            if result["total_travel"] < best["total_travel"]:
                                best = result
        if feasible_found_for_r:
            break  # no need to consider smaller subsets

    output = {"itinerary": best["itinerary"] if best else []}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()