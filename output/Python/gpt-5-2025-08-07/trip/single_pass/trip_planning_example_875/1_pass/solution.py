import itertools
import json

def compute_itinerary():
    # Input variables (constraints)
    total_days = 20
    city_durations = {
        "Stuttgart": 3,
        "Edinburgh": 4,
        "Athens": 4,
        "Split": 2,
        "Krakow": 4,
        "Venice": 5,
        "Mykonos": 4,
    }
    # Required presence windows (inclusive): must be in the city for the entire window
    windows = {
        "Stuttgart": (11, 13),  # workshop days
        "Split": (13, 14),      # meet friends
        "Krakow": (8, 11),      # meet a friend
    }

    # Direct flight connections (undirected)
    direct_pairs = [
        ("Krakow", "Split"),
        ("Split", "Athens"),
        ("Edinburgh", "Krakow"),
        ("Venice", "Stuttgart"),
        ("Krakow", "Stuttgart"),
        ("Edinburgh", "Stuttgart"),
        ("Stuttgart", "Athens"),
        ("Venice", "Edinburgh"),
        ("Athens", "Mykonos"),
        ("Venice", "Athens"),
        ("Stuttgart", "Split"),
        ("Edinburgh", "Athens"),
    ]

    # Build adjacency set for quick lookup
    adjacency = set()
    for a, b in direct_pairs:
        adjacency.add((a, b))
        adjacency.add((b, a))

    cities = list(city_durations.keys())
    n = len(cities)

    # Feasibility check for total span with overlap rule:
    # Sum(durations) - (n - 1) must equal total_days
    if sum(city_durations.values()) - (n - 1) != total_days:
        raise ValueError("Durations do not align with total days under overlap rule.")

    def is_connected_path(order):
        return all((order[i], order[i + 1]) in adjacency for i in range(len(order) - 1))

    def compute_ranges(order):
        # Using overlap rule: next segment starts on the same day the previous ends
        itinerary = []
        start_day = 1
        for city in order:
            end_day = start_day + city_durations[city] - 1
            itinerary.append((city, start_day, end_day))
            start_day = end_day  # overlap on transition day
        return itinerary

    def windows_satisfied(itinerary):
        city_to_range = {city: (s, e) for city, s, e in itinerary}
        for city, (L, U) in windows.items():
            if city not in city_to_range:
                return False
            s, e = city_to_range[city]
            if not (s <= L and e >= U):
                return False
        return True

    # Search for an optimal (first-valid) itinerary
    best_itinerary = None
    # Use sorted order for deterministic search
    for order in itertools.permutations(sorted(cities)):
        if not is_connected_path(order):
            continue
        itinerary = compute_ranges(order)
        # Ensure final day matches total_days
        if itinerary[-1][2] != total_days:
            continue
        if not windows_satisfied(itinerary):
            continue
        # Passed all constraints; pick first valid as optimal
        best_itinerary = itinerary
        break

    if best_itinerary is None:
        # If no valid itinerary is found, return empty structure (should not happen for this input)
        output = {"itinerary": []}
    else:
        formatted = []
        for city, s, e in best_itinerary:
            formatted.append({
                "day_range": f"Day {s}-{e}",
                "place": city
            })
        output = {"itinerary": formatted}

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    compute_itinerary()