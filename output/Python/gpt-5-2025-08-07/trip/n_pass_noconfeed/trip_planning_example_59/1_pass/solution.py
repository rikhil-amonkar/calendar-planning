import itertools
import json

def find_itinerary(total_days, required_days, direct_flights, wedding_city, wedding_window):
    # Build undirected adjacency for direct flights
    edges = {tuple(sorted(edge)) for edge in direct_flights}
    cities = list(required_days.keys())

    def direct(a, b):
        return tuple(sorted((a, b))) in edges

    def interval_intersection(a, b):
        # a, b are tuples (start, end), inclusive
        start = max(a[0], b[0])
        end = min(a[1], b[1])
        return max(0, end - start + 1)

    # Sum of required city-days must equal total_days + number_of_flights (2 for 3 cities path)
    flights_count = 2
    if sum(required_days.values()) != total_days + flights_count:
        return None

    # Try all permutations and pick the first feasible one that satisfies constraints
    for order in itertools.permutations(cities, 3):
        c1, c2, c3 = order

        # Must be a valid path c1 -> c2 -> c3 via direct flights only
        if not (direct(c1, c2) and direct(c2, c3)):
            continue

        # Compute flight days and city intervals using overlap rule:
        # d1 = end of first segment (also flight day to c2)
        # d2 = end of second segment (also flight day to c3)
        d1 = required_days[c1]
        d2 = required_days[c1] + required_days[c2] - 1

        # Validate interval bounds
        if not (1 <= d1 <= total_days and 1 <= d2 <= total_days and d1 <= d2):
            continue

        # Validate third city's required days match the remainder with overlap on d2
        r3_calc = total_days - d2 + 1
        if r3_calc != required_days[c3]:
            continue

        # Build intervals (inclusive)
        intervals = {
            c1: (1, d1),
            c2: (d1, d2),
            c3: (d2, total_days)
        }

        # Wedding constraint: be in wedding_city on at least one day in the wedding_window
        if wedding_city not in intervals:
            continue
        if interval_intersection(intervals[wedding_city], wedding_window) <= 0:
            continue

        # Verify each city's days match required (with overlap counted as instructed)
        for city in cities:
            start, end = intervals[city]
            if (end - start + 1) != required_days[city]:
                break
        else:
            # Construct itinerary entries; overlapping boundaries reflect flight days counted in both cities
            itinerary = [
                {"day_range": f"Day {intervals[c1][0]}-{intervals[c1][1]}", "place": c1},
                {"day_range": f"Day {intervals[c2][0]}-{intervals[c2][1]}", "place": c2},
                {"day_range": f"Day {intervals[c3][0]}-{intervals[c3][1]}", "place": c3},
            ]
            return itinerary

    return None

if __name__ == "__main__":
    # Input variables (constraints)
    total_days = 16
    required_days = {
        "Lyon": 7,
        "Bucharest": 7,
        "Porto": 4
    }
    direct_flights = [
        ("Bucharest", "Lyon"),
        ("Lyon", "Porto")
    ]
    wedding_city = "Bucharest"
    wedding_window = (1, 7)  # inclusive

    itinerary = find_itinerary(total_days, required_days, direct_flights, wedding_city, wedding_window)
    if itinerary is None:
        output = {"error": "No feasible itinerary found with the given constraints."}
    else:
        output = {"itinerary": itinerary}

    print(json.dumps(output, ensure_ascii=False))