import json
import itertools
from collections import defaultdict

def compute_itinerary():
    # Input variables (constraints)
    total_days = 13
    cities = ["Madrid", "Seville", "Porto", "Stuttgart"]

    # Required days in each city
    required_days = {
        "Seville": 2,
        "Stuttgart": 7,
        "Porto": 3,
        "Madrid": 4
    }

    # Direct flight connections (undirected)
    direct_flights = {
        ("Porto", "Stuttgart"),
        ("Seville", "Porto"),
        ("Madrid", "Porto"),
        ("Madrid", "Seville"),
    }

    # Conference constraints: must be in Stuttgart on these days
    must_be_in_city_on_day = {7: "Stuttgart", 13: "Stuttgart"}

    # Relatives visit: must be in Madrid on days 1 through 4 inclusive
    relatives_city = "Madrid"
    relatives_day_range = range(1, 5)  # Day 1..4 inclusive

    # Helper functions
    def is_direct(a, b):
        return (a, b) in direct_flights or (b, a) in direct_flights

    # Quick feasibility checks
    sum_required = sum(required_days[c] for c in cities)
    min_flights_needed = len(cities) - 1  # visiting each city once, in a path
    # Unique total days = sum(city-days) - number_of_flight_days (overlaps)
    if sum_required - min_flights_needed != total_days:
        # If this fails, no solution can exist in a linear path visiting each city once
        return None

    best_solution = None

    # Try all permutations of the cities to represent the visiting order
    for order in itertools.permutations(cities):
        # Enforce that all consecutive transitions are direct flights
        if not all(is_direct(order[i], order[i+1]) for i in range(len(order)-1)):
            continue

        # Build city blocks with overlap on transition days:
        # If city A is days s..e and next city B starts on day e (flight day),
        # both A and B include day e.
        day_blocks = {}  # city -> (start_day, end_day)
        current_start = 1
        valid = True

        for i, city in enumerate(order):
            dur = required_days[city]
            # For first city, start at day 1
            if i == 0:
                start = current_start
                end = start + dur - 1
            else:
                # Overlap with previous end day (flight day)
                start = current_start  # current_start already equals previous end
                end = start + dur - 1
            day_blocks[city] = (start, end)
            current_start = end  # next city starts at this 'end' (overlap/flight day)

        # Check total unique days span equals total_days
        last_city = order[-1]
        if day_blocks[last_city][1] != total_days:
            continue

        # Build a day->set(cities) inclusion map accounting for overlaps
        day_inclusions = defaultdict(set)
        for city, (s, e) in day_blocks.items():
            for d in range(s, e + 1):
                day_inclusions[d].add(city)

        # Validate required day counts per city
        counts = {c: 0 for c in cities}
        for d in range(1, total_days + 1):
            for c in day_inclusions[d]:
                counts[c] += 1
        if counts != required_days:
            continue

        # Validate conference presence in Stuttgart on required days
        ok_conf = True
        for day, city in must_be_in_city_on_day.items():
            if city not in day_inclusions[day]:
                ok_conf = False
                break
        if not ok_conf:
            continue

        # Validate relatives visit: must be in Madrid on every day in relatives_day_range
        if not all(relatives_city in day_inclusions[d] for d in relatives_day_range):
            continue

        # All constraints satisfied; select this as solution
        itinerary = []
        for city in order:
            s, e = day_blocks[city]
            itinerary.append({
                "day_range": f"Day {s}-{e}",
                "place": city
            })

        best_solution = {"itinerary": itinerary}
        break

    return best_solution

def main():
    result = compute_itinerary()
    if result is None:
        print(json.dumps({"error": "No feasible itinerary found with given constraints"}))
    else:
        print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()