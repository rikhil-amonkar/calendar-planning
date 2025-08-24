import itertools
import json
from typing import List, Dict, Tuple, Optional

def is_direct(a: str, b: str, direct_pairs: List[Tuple[str, str]]) -> bool:
    return (a, b) in direct_pairs or (b, a) in direct_pairs

def compute_schedule(order: List[str],
                     durations: Dict[str, int],
                     direct_pairs: List[Tuple[str, str]],
                     windows: Dict[str, Tuple[int, int]],
                     total_days: int) -> Optional[List[Dict[str, int]]]:
    # Build schedule with overlap travel: start_next = end_prev (flight on same day)
    schedule = []
    start = 1
    for idx, city in enumerate(order):
        length = durations[city]
        if idx == 0:
            s = start
        else:
            # must have direct connection from previous city
            prev_city = order[idx - 1]
            if not is_direct(prev_city, city, direct_pairs):
                return None
            # Flight on the same day as prev_city's end day
            s = schedule[-1]["end"]
        e = s + length - 1
        schedule.append({"city": city, "start": s, "end": e})
    # Check total unique days
    if schedule[-1]["end"] != total_days:
        return None
    # Check window coverage constraints: the trip must fully cover the specified window
    # i.e., be present for the entire window [a, b]
    for city, (a, b) in windows.items():
        seg = next((seg for seg in schedule if seg["city"] == city), None)
        if seg is None:
            return None
        if not (seg["start"] <= a and seg["end"] >= b):
            return None
    return schedule

def main():
    # Input variables derived from the trip constraints
    total_days = 18
    cities = ["Tallinn", "Bucharest", "Seville", "Stockholm", "Munich", "Milan"]

    # Desired stays (days in each city). Travel days count in both adjacent cities by design.
    durations = {
        "Tallinn": 2,     # plan to stay for 2 days
        "Bucharest": 4,   # plan to stay for 4 days
        "Seville": 5,     # want to spend 5 days
        "Stockholm": 5,   # would like 5 days
        "Munich": 5,      # plan to stay for 5 days
        "Milan": 2        # would like 2 days
    }

    # Direct flights (undirected)
    direct_pairs = [
        ("Milan", "Stockholm"),
        ("Munich", "Stockholm"),
        ("Bucharest", "Munich"),
        ("Munich", "Seville"),
        ("Stockholm", "Tallinn"),
        ("Munich", "Milan"),
        ("Munich", "Tallinn"),
        ("Seville", "Milan")
    ]

    # Time window constraints (must be present throughout the window)
    # Bucharest between day 1 and day 4
    # Munich wedding between day 4 and day 8
    # Seville friends between day 8 and day 12
    windows = {
        "Bucharest": (1, 4),
        "Munich": (4, 8),
        "Seville": (8, 12)
    }

    # Quick feasibility check: unique days from durations with N segments and N-1 overlaps
    sum_durations = sum(durations[c] for c in cities)
    required_unique_days = sum_durations - (len(cities) - 1)
    if required_unique_days != total_days:
        # No possible schedule matches total unique days with these exact durations
        print(json.dumps({"itinerary": []}))
        return

    # Try all permutations to find a valid itinerary that respects direct flights and windows
    valid_schedule = None
    for perm in itertools.permutations(cities):
        schedule = compute_schedule(list(perm), durations, direct_pairs, windows, total_days)
        if schedule is not None:
            valid_schedule = schedule
            break

    if not valid_schedule:
        print(json.dumps({"itinerary": []}))
        return

    # Build output JSON structure
    itinerary_output = []
    for seg in valid_schedule:
        itinerary_output.append({
            "day_range": f"Day {seg['start']}-{seg['end']}",
            "place": seg["city"]
        })

    print(json.dumps({"itinerary": itinerary_output}, ensure_ascii=False))

if __name__ == "__main__":
    main()