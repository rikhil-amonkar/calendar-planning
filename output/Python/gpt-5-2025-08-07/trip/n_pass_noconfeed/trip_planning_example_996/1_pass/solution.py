import json
import itertools

def main():
    # Input variables (constraints)
    total_days = 22
    city_durations = {
        "Valencia": 5,
        "Riga": 5,
        "Prague": 3,
        "Mykonos": 3,
        "Zurich": 5,
        "Bucharest": 5,
        "Nice": 2,
    }
    cities = list(city_durations.keys())

    # Direct flights (undirected)
    direct_pairs = [
        ("Mykonos", "Nice"),
        ("Mykonos", "Zurich"),
        ("Prague", "Bucharest"),
        ("Valencia", "Bucharest"),
        ("Zurich", "Prague"),
        ("Riga", "Nice"),
        ("Zurich", "Riga"),
        ("Zurich", "Bucharest"),
        ("Zurich", "Valencia"),
        ("Bucharest", "Riga"),
        ("Prague", "Riga"),
        ("Prague", "Valencia"),
        ("Zurich", "Nice"),
    ]
    direct_edges = set(frozenset({a, b}) for a, b in direct_pairs)

    # Must-be-in-city windows (inclusive), days are global Day 1..Day 22
    # Requirement: be in Mykonos on Days 1-3, and Prague on Days 7-9
    must_cover = {
        "Mykonos": [(1, 3)],
        "Prague": [(7, 9)],
    }

    # Helper: check if an itinerary order uses only direct flights
    def is_direct_chain(order):
        for i in range(len(order) - 1):
            if frozenset({order[i], order[i + 1]}) not in direct_edges:
                return False
        return True

    # Compute start/end days for each city given an order and durations
    # Rules:
    # - Start Day for first city is 1
    # - Flight day overlaps: start(next) = end(current)
    def compute_schedule(order):
        starts = {}
        ends = {}
        starts[order[0]] = 1
        ends[order[0]] = starts[order[0]] + city_durations[order[0]] - 1
        for i in range(1, len(order)):
            prev = order[i - 1]
            cur = order[i]
            starts[cur] = ends[prev]  # overlapping flight day
            ends[cur] = starts[cur] + city_durations[cur] - 1
        return starts, ends

    # Verify must-cover windows (city must include entire window)
    def satisfies_windows(starts, ends):
        for city, windows in must_cover.items():
            if city not in starts:
                return False
            s = starts[city]
            e = ends[city]
            for ws, we in windows:
                if not (s <= ws and e >= we):
                    return False
        return True

    # Ensure overall trip ends on total_days
    def ends_on_total_days(order, ends):
        return ends[order[-1]] == total_days

    # Sanity: sum of durations must equal total_days + number_of_flights (N-1)
    n = len(cities)
    if sum(city_durations.values()) != total_days + (n - 1):
        # If this fails, no schedule can satisfy all durations with overlaps
        result = {"itinerary": [], "error": "Durations and total days are inconsistent with overlap rule."}
        print(json.dumps(result))
        return

    # Search for a valid itinerary order satisfying all constraints
    solution = None
    # Logical pruning: because Mykonos must include Days 1-3 and has duration 3,
    # it must be the first city (start at Day 1).
    # We'll reduce permutations by fixing Mykonos as the first city.
    remaining = [c for c in cities if c != "Mykonos"]
    for perm_tail in itertools.permutations(remaining):
        order = ("Mykonos",) + perm_tail
        if not is_direct_chain(order):
            continue
        starts, ends = compute_schedule(order)
        if not satisfies_windows(starts, ends):
            continue
        if not ends_on_total_days(order, ends):
            continue
        solution = (order, starts, ends)
        break

    if solution is None:
        result = {"itinerary": [], "error": "No valid itinerary found that satisfies all constraints."}
        print(json.dumps(result))
        return

    order, starts, ends = solution
    itinerary = []
    for city in order:
        itinerary.append({
            "day_range": f"Day {starts[city]}-{ends[city]}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()