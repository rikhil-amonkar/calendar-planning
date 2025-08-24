import json
from itertools import permutations

def main():
    # Input variables (constraints)
    total_days = 12
    cities = ["Prague", "Berlin", "Tallinn", "Stockholm"]
    required_days = {
        "Prague": 2,
        "Berlin": 3,
        "Tallinn": 5,
        "Stockholm": 5,
    }
    # Conference days in Berlin
    berlin_conference_days = {6, 8}
    # Must be in Tallinn from day 8 to 12 (inclusive)
    tallinn_relatives_window = set(range(8, 13))
    # Direct flight connectivity (undirected)
    direct_flights = {
        ("Berlin", "Tallinn"),
        ("Prague", "Tallinn"),
        ("Stockholm", "Tallinn"),
        ("Prague", "Stockholm"),
        ("Stockholm", "Berlin"),
    }

    # Prepare undirected adjacency for lookups
    adjacency = {frozenset(edge) for edge in direct_flights}

    def is_direct(a, b):
        return frozenset((a, b)) in adjacency

    # Expected number of flight days from counting rule
    flights_needed = sum(required_days[c] for c in cities) - total_days

    # For visiting 4 cities in a single chain we inherently have 3 flights
    chain_flights = 3
    if flights_needed != chain_flights:
        # If constraints are inconsistent, no solution will be found;
        # but we continue to attempt a search just in case.
        pass

    # Helper: compute city intervals for an order and flight days
    # order = [C0, C1, C2, C3], flights on d1<d2<d3
    # City intervals (inclusive):
    # C0: [1, d1], C1: [d1, d2], C2: [d2, d3], C3: [d3, total_days]
    def compute_intervals(order, d1, d2, d3):
        return {
            order[0]: (1, d1),
            order[1]: (d1, d2),
            order[2]: (d2, d3),
            order[3]: (d3, total_days),
        }

    def count_days(interval):
        a, b = interval
        return b - a + 1

    def day_in_city(intervals, city, day):
        a, b = intervals[city]
        return a <= day <= b

    # Search over possible city orders and flight days
    candidates = []
    for order in permutations(cities, 4):
        # Must visit all 4 cities exactly once
        if len(set(order)) != 4:
            continue
        # Only take direct flights between consecutive cities in the order
        if not (is_direct(order[0], order[1]) and is_direct(order[1], order[2]) and is_direct(order[2], order[3])):
            continue

        # Iterate over strictly increasing flight days within 1..12
        # d1<d2<d3
        for d1 in range(1, total_days - 1):          # at least 1, at most 10
            for d2 in range(d1 + 1, total_days):     # at most 11
                for d3 in range(d2 + 1, total_days + 1):  # at most 12
                    intervals = compute_intervals(order, d1, d2, d3)

                    # Check required day counts per city
                    ok_counts = True
                    for city in cities:
                        if count_days(intervals[city]) != required_days[city]:
                            ok_counts = False
                            break
                    if not ok_counts:
                        continue

                    # Must be in Berlin on the conference days
                    if not all(day_in_city(intervals, "Berlin", d) for d in berlin_conference_days):
                        continue

                    # Must be in Tallinn for every day 8..12
                    if not all(day_in_city(intervals, "Tallinn", d) for d in tallinn_relatives_window):
                        continue

                    # At this point, we have a valid candidate
                    # Define a simple optimality criterion:
                    # - Minimize flight day tuple lex order (earliest possible flights)
                    # - Then lex order of city order for determinism
                    score = (d1, d2, d3, tuple(order))
                    candidates.append((score, order, (d1, d2, d3), intervals))

    if not candidates:
        result = {"itinerary": []}
        print(json.dumps(result, ensure_ascii=False))
        return

    # Choose the optimal candidate by our scoring rule
    candidates.sort(key=lambda x: x[0])
    _, best_order, (bd1, bd2, bd3), best_intervals = candidates[0]

    # Build itinerary as list of day ranges
    # Ranges include flight days for both adjacent cities as required
    # C0: Day 1-bd1, C1: Day bd1-bd2, C2: Day bd2-bd3, C3: Day bd3-12
    itinerary = [
        {"day_range": f"Day {1}-{bd1}", "place": best_order[0]},
        {"day_range": f"Day {bd1}-{bd2}", "place": best_order[1]},
        {"day_range": f"Day {bd2}-{bd3}", "place": best_order[2]},
        {"day_range": f"Day {bd3}-{total_days}", "place": best_order[3]},
    ]

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()