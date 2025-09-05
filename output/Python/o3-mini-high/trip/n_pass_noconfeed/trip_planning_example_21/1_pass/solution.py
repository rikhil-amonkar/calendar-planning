#!/usr/bin/env python3
import json
from itertools import permutations

def main():
    # Input constraints
    total_days = 10
    workshop_city = "Venice"
    workshop_window_start = 5
    workshop_window_end = 10

    # Required durations in each city (in days)
    durations = {
        "Venice": 6,
        "Mykonos": 2,
        "Vienna": 4
    }

    # List of cities (must be exactly 3)
    cities = list(durations.keys())

    # Direct flight connections (assumed bidirectional)
    # Only direct flights allowed: Mykonos <-> Vienna and Vienna <-> Venice.
    direct_flights = [
        ("Mykonos", "Vienna"),
        ("Vienna", "Venice")
    ]

    # Build a flight connectivity graph
    flight_graph = {}
    for (a, b) in direct_flights:
        flight_graph.setdefault(a, set()).add(b)
        flight_graph.setdefault(b, set()).add(a)

    # Function to check if a given ordering has direct flights between successive cities.
    def is_valid_order(order):
        for i in range(len(order) - 1):
            if order[i+1] not in flight_graph.get(order[i], set()):
                return False
        return True

    # Function to compute itinerary segments with overlapping flight days.
    # If you fly from A to B on day X, day X counts for both A and B.
    def compute_segments(order):
        segments = []
        current_day = 1
        for city in order:
            duration = durations[city]
            # The segment runs from the current day to current_day + duration - 1.
            start_day = current_day
            end_day = current_day + duration - 1
            segments.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
            # The next city is entered on the same day as the current segment's end.
            current_day = end_day
        return segments, current_day

    # Try all permutations that satisfy flight connectivity and check total trip days.
    valid_itinerary = None
    valid_segments = None
    for order in permutations(cities):
        if not is_valid_order(order):
            continue
        segments, final_day = compute_segments(order)
        # The trip must exactly cover the required total number of days.
        if final_day != total_days:
            continue
        # Check the workshop constraint: the workshop in Venice must occur between day 5 and day 10.
        venice_range = None
        for seg in segments:
            if seg["place"] == workshop_city:
                # Extract start and end day from the day_range string.
                day_part = seg["day_range"].replace("Day ", "")
                start_str, end_str = day_part.split("-")
                venice_range = (int(start_str), int(end_str))
                break
        if venice_range is None:
            continue
        # The Venice segment must overlap the workshop window.
        if venice_range[1] < workshop_window_start or venice_range[0] > workshop_window_end:
            continue
        # Found a valid itinerary that meets all constraints.
        valid_itinerary = order
        valid_segments = segments
        break

    # Final JSON output
    if valid_segments is None:
        output = {"error": "No valid itinerary found"}
    else:
        output = {"itinerary": valid_segments}
    print(json.dumps(output))

if __name__ == "__main__":
    main()