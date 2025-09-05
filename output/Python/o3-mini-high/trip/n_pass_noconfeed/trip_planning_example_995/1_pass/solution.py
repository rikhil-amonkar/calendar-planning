#!/usr/bin/env python3
import itertools
import json

def main():
    # Total itinerary parameters
    total_days = 16
    # List of cities to visit
    cities = ["Barcelona", "Oslo", "Stuttgart", "Venice", "Split", "Brussels", "Copenhagen"]

    # Required durations (in days) for each city
    durations = {
        "Barcelona": 3,
        "Oslo": 2,
        "Stuttgart": 3,
        "Venice": 4,
        "Split": 4,
        "Brussels": 3,
        "Copenhagen": 3
    }

    # Meeting/event constraints (inclusive windows)
    # In Barcelona there is an annual show from Day 1 to Day 3.
    annual_show_window = (1, 3)
    # Meet friends in Oslo between Day 3 and Day 4.
    oslo_meeting_window = (3, 4)
    # Meet a friend in Brussels between Day 9 and Day 11.
    brussels_meeting_window = (9, 11)

    # Direct flight connectivity (bidirectional)
    flight_pairs = [
        ("Venice", "Stuttgart"),
        ("Oslo", "Brussels"),
        ("Split", "Copenhagen"),
        ("Barcelona", "Copenhagen"),
        ("Barcelona", "Venice"),
        ("Brussels", "Venice"),
        ("Barcelona", "Stuttgart"),
        ("Copenhagen", "Brussels"),
        ("Oslo", "Split"),
        ("Oslo", "Venice"),
        ("Barcelona", "Split"),
        ("Oslo", "Copenhagen"),
        ("Barcelona", "Oslo"),
        ("Copenhagen", "Stuttgart"),
        ("Split", "Stuttgart"),
        ("Copenhagen", "Venice"),
        ("Barcelona", "Brussels")
    ]

    # Build the undirected flight graph
    graph = {city: set() for city in cities}
    for city_a, city_b in flight_pairs:
        graph[city_a].add(city_b)
        graph[city_b].add(city_a)

    # For the itinerary, Barcelona must be first (to attend the show)
    # and Oslo must be visited soon to meet friends between Day 3 and 4.
    fixed_order = ["Barcelona", "Oslo"]
    remaining_cities = [city for city in cities if city not in fixed_order]

    valid_itinerary = None

    # Try all orders of the remaining cities
    for perm in itertools.permutations(remaining_cities):
        itinerary_order = fixed_order + list(perm)

        # Check flight connectivity between consecutive cities
        valid_flights = True
        for i in range(len(itinerary_order) - 1):
            current_city = itinerary_order[i]
            next_city = itinerary_order[i + 1]
            if next_city not in graph[current_city]:
                valid_flights = False
                break
        if not valid_flights:
            continue

        # Compute day intervals for each city.
        # Rule: The first city starts at Day 1 and gets its full duration.
        # For subsequent cities, the arrival day is the same as the departure day of the previous city.
        current_day = 1
        itinerary_segments = []
        day_intervals = {}
        for city in itinerary_order:
            start_day = current_day
            end_day = start_day + durations[city] - 1
            day_intervals[city] = (start_day, end_day)
            itinerary_segments.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city
            })
            current_day = end_day  # Next city starts on the same day as this city's end (flight day overlap)
        if current_day != total_days:
            continue

        # Check meeting constraints:
        # Barcelona must cover the annual show period (Day 1-3).
        barcelona_start, barcelona_end = day_intervals["Barcelona"]
        if not (barcelona_start <= annual_show_window[0] and barcelona_end >= annual_show_window[1]):
            continue

        # Oslo must allow meeting between Day 3 and 4.
        oslo_start, oslo_end = day_intervals["Oslo"]
        if not (oslo_end >= oslo_meeting_window[0] and oslo_start <= oslo_meeting_window[1]):
            continue

        # Brussels must allow meeting between Day 9 and 11.
        if "Brussels" in day_intervals:
            brussels_start, brussels_end = day_intervals["Brussels"]
            if not (brussels_end >= brussels_meeting_window[0] and brussels_start <= brussels_meeting_window[1]):
                continue

        # Found a valid itinerary that meets all constraints.
        valid_itinerary = {"itinerary": itinerary_segments}
        break

    if valid_itinerary is None:
        valid_itinerary = {"itinerary": []}
    print(json.dumps(valid_itinerary))

if __name__ == "__main__":
    main()