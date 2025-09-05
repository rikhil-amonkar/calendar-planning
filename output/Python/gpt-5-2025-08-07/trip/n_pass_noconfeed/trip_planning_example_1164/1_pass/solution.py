import json
import itertools

def main():
    # Input variables (trip constraints)
    total_days = 17
    cities = [
        "Reykjavik", "Stockholm", "Porto", "Nice",
        "Venice", "Vienna", "Split", "Copenhagen"
    ]
    durations = {
        "Reykjavik": 2,
        "Stockholm": 2,
        "Porto": 5,
        "Nice": 3,
        "Venice": 4,
        "Vienna": 3,
        "Split": 3,
        "Copenhagen": 2
    }
    # Direct flights (undirected)
    direct_pairs = [
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
        ("Copenhagen", "Porto")
    ]
    # Build adjacency map
    adjacency = {c: set() for c in cities}
    for a, b in direct_pairs:
        adjacency[a].add(b)
        adjacency[b].add(a)

    # Verify durations sum to total_days + (n_cities - 1) due to overlap rule
    if sum(durations.values()) != total_days + (len(cities) - 1):
        raise ValueError("Durations do not sum to total allowable with overlaps.")

    # Required day inclusion constraints (inclusive)
    # "between day X and day Y" is interpreted as city must include both X and Y
    required_inclusions = {
        "Reykjavik": set([3, 4]),
        "Stockholm": set([4, 5]),
        "Vienna": set(range(11, 14)),  # 11,12,13
        "Porto": set(range(13, 18)),   # 13..17
    }

    # Helper to compute intervals given an order
    def compute_intervals(order):
        intervals = {}
        start = 1
        for city in order:
            end = start + durations[city] - 1
            intervals[city] = (start, end)
            start = end  # overlap by 1 day with next city (flight day)
        return intervals

    # Check if order is valid:
    def is_valid_order(order):
        # Check direct flights between consecutive cities
        for i in range(len(order) - 1):
            if order[i+1] not in adjacency[order[i]]:
                return False

        # Compute intervals and ensure last day matches total_days
        intervals = compute_intervals(order)
        last_city = order[-1]
        if intervals[last_city][1] != total_days:
            return False

        # Check required day inclusions
        for city, days in required_inclusions.items():
            start, end = intervals[city]
            city_days = set(range(start, end + 1))
            if not days.issubset(city_days):
                return False

        return True

    # Generate and search permutations algorithmically
    # To reduce search, enforce Porto is last because it must include day 17.
    remaining_cities = [c for c in cities if c != "Porto"]

    solution_order = None
    for perm in itertools.permutations(remaining_cities):
        order = list(perm) + ["Porto"]
        if is_valid_order(order):
            solution_order = order
            break

    if solution_order is None:
        raise RuntimeError("No valid itinerary found under given constraints.")

    # Build itinerary output with day ranges
    intervals = compute_intervals(solution_order)
    itinerary = []
    for city in solution_order:
        start, end = intervals[city]
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    # Output JSON
    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()