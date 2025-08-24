import itertools
import json

def main():
    # Input variables
    total_days = 17
    cities = [
        "Reykjavik",
        "Stockholm",
        "Porto",
        "Nice",
        "Venice",
        "Vienna",
        "Split",
        "Copenhagen",
    ]
    durations = {
        "Reykjavik": 2,
        "Stockholm": 2,
        "Porto": 5,
        "Nice": 3,
        "Venice": 4,
        "Vienna": 3,
        "Split": 3,
        "Copenhagen": 2,
    }
    # Windows: must be present in the city on at least one day in the inclusive range
    windows = {
        "Reykjavik": (3, 4),  # meet a friend between day 3 and 4
        "Stockholm": (4, 5),  # meet friends between day 4 and 5
        "Vienna": (11, 13),   # workshop between day 11 and 13
        "Porto": (13, 17),    # wedding between day 13 and 17
    }
    # Direct flights (undirected edges)
    flight_pairs = [
        ("Copenhagen", "Vienna"),
        ("Nice", "Stockholm"),
        ("Split", "Copenhagen"),
        ("Nice", "Reykjavik"),
        ("Nice", "Porto"),
        ("Reykjavik", "Vienna"),
        ("Stockholm", "Copenhagen"),
        ("Nice", "Venice"),
        ("Nice", "Vienna"),
        ("Reykjavik", "Copenhagen"),
        ("Nice", "Copenhagen"),
        ("Stockholm", "Vienna"),
        ("Venice", "Vienna"),
        ("Copenhagen", "Venice"),
        ("Vienna", "Porto"),
        ("Reykjavik", "Stockholm"),
        ("Stockholm", "Split"),
        ("Split", "Vienna"),
        ("Copenhagen", "Porto"),
    ]
    flights = {frozenset((a, b)) for a, b in flight_pairs}

    def compute_intervals(order):
        start = 1
        intervals = {}
        for city in order:
            end = start + durations[city] - 1
            intervals[city] = (start, end)
            start = end  # travel on 'end' day overlaps with next city start
        return intervals

    def windows_satisfied(intervals):
        for city, (ws, we) in windows.items():
            cs, ce = intervals[city]
            # Must intersect at least one day in the window
            if ce < ws or cs > we:
                return False
        return True

    def flights_satisfied(order):
        for i in range(len(order) - 1):
            if frozenset((order[i], order[i + 1])) not in flights:
                return False
        return True

    # Sanity check: total sum of durations - (number_of_cities - 1) must equal total_days
    sum_durations = sum(durations[c] for c in cities)
    if sum_durations - (len(cities) - 1) != total_days:
        raise ValueError("Durations and number of cities cannot produce the requested total days with overlaps.")

    solution = None
    # Search for a feasible itinerary
    for order in itertools.permutations(cities):
        intervals = compute_intervals(order)
        # Ensure final day equals total_days
        if intervals[order[-1]][1] != total_days:
            continue
        if not flights_satisfied(order):
            continue
        if not windows_satisfied(intervals):
            continue
        solution = [(city, intervals[city][0], intervals[city][1]) for city in order]
        break

    if not solution:
        raise RuntimeError("No feasible itinerary found that satisfies all constraints.")

    # Build JSON output
    itinerary = []
    for city, s, e in solution:
        itinerary.append({"day_range": f"Day {s}-{e}", "place": city})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()