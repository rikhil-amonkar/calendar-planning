import json
from itertools import permutations

def compute_itinerary():
    # Input variables (constraints)
    total_days = 11
    required_days = {
        "Seville": 6,
        "Paris": 2,
        "Krakow": 5
    }
    direct_flights_input = [("Krakow", "Paris"), ("Paris", "Seville")]  # Given connections
    workshop_city = "Krakow"
    workshop_window = (1, 5)  # inclusive

    # Build bidirectional flight set
    direct_flights = set()
    for a, b in direct_flights_input:
        direct_flights.add((a, b))
        direct_flights.add((b, a))

    cities = list(required_days.keys())
    sum_required = sum(required_days.values())
    min_flights_needed = sum_required - total_days
    if min_flights_needed != 2:
        raise ValueError("Infeasible constraints: expected exactly 2 flight days based on totals.")

    # Generate feasible linear routes of 3 cities following direct flight edges A->B->C
    candidate_routes = []
    for route in permutations(cities, 3):
        if (route[0], route[1]) in direct_flights and (route[1], route[2]) in direct_flights:
            candidate_routes.append(route)

    def days_for_city_segments(route, total_days, required_days):
        # For a linear route A->B->C with exactly 2 flight days:
        # City A occupies Day 1..d1
        # City B occupies Day d1..d2
        # City C occupies Day d2..total_days
        # Where flight days are d1 (A->B) and d2 (B->C)
        A, B, C = route
        d1 = required_days[A]  # ensures A totals match
        d2 = total_days - required_days[C] + 1  # ensures C totals match
        # Validate B totals match required
        if d2 - d1 + 1 != required_days[B]:
            return None
        if not (1 <= d1 <= total_days and 1 <= d2 <= total_days and d2 >= d1):
            return None
        return {
            A: (1, d1),
            B: (d1, d2),
            C: (d2, total_days),
            "_d1": d1,
            "_d2": d2
        }

    def workshop_satisfied(segments, workshop_city, window):
        start, end = segments[workshop_city]
        ws, we = window
        return not (end < ws or start > we)

    chosen = None
    for route in candidate_routes:
        segments = days_for_city_segments(route, total_days, required_days)
        if segments is None:
            continue
        if not workshop_satisfied(segments, workshop_city, workshop_window):
            continue
        chosen = (route, segments)
        break

    if chosen is None:
        raise ValueError("No feasible itinerary found that meets all constraints.")

    route, segments = chosen
    A, B, C = route
    d1 = segments["_d1"]
    d2 = segments["_d2"]

    itinerary = [
        {"day_range": f"Day {segments[A][0]}-{segments[A][1]}", "place": A},
        {"day_range": f"Day {segments[B][0]}-{segments[B][1]}", "place": B},
        {"day_range": f"Day {segments[C][0]}-{segments[C][1]}", "place": C},
    ]

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result))