import json

def build_flight_graph():
    edges = {}
    def add(a, b):
        edges.setdefault(a, set()).add(b)
    def add_bi(a, b):
        add(a, b)
        add(b, a)

    # Build directed flight graph from the provided constraints
    add_bi("Riga", "Prague")
    add_bi("Stockholm", "Milan")
    add_bi("Riga", "Milan")
    add_bi("Lisbon", "Stockholm")
    add("Stockholm", "Santorini")  # one-way
    add_bi("Naples", "Warsaw")
    add_bi("Lisbon", "Warsaw")
    add_bi("Naples", "Milan")
    add_bi("Lisbon", "Naples")
    add("Riga", "Tallinn")  # one-way
    add_bi("Tallinn", "Prague")
    add_bi("Stockholm", "Warsaw")
    add_bi("Riga", "Warsaw")
    add_bi("Lisbon", "Riga")
    add_bi("Riga", "Stockholm")
    add_bi("Lisbon", "Porto")
    add_bi("Lisbon", "Prague")
    add_bi("Milan", "Porto")
    add_bi("Prague", "Milan")
    add_bi("Lisbon", "Milan")
    add_bi("Warsaw", "Porto")
    add_bi("Warsaw", "Tallinn")
    add_bi("Santorini", "Milan")
    add_bi("Stockholm", "Prague")
    add_bi("Stockholm", "Tallinn")
    add_bi("Warsaw", "Milan")
    add_bi("Santorini", "Naples")
    add_bi("Warsaw", "Prague")
    return edges

def find_itinerary():
    total_days = 28
    # City durations (exact days counted including flight overlap days at block boundaries)
    durations = {
        "Prague": 5,
        "Tallinn": 3,
        "Warsaw": 2,
        "Porto": 3,
        "Naples": 5,
        "Milan": 3,
        "Lisbon": 5,
        "Santorini": 5,
        "Riga": 4,
        "Stockholm": 2,
    }

    # Pinned start days for specific events
    pinned_starts = {
        "Riga": 5,       # Day 5-8 Riga show
        "Tallinn": 18,   # Day 18-20 relatives
        "Milan": 24      # Day 24-26 friend meeting
    }

    # Build directed graph of flights
    edges = build_flight_graph()

    cities = list(durations.keys())
    n_cities = len(cities)

    # Validate totals: unique days = sum(durations) - (n_cities - 1)
    assert sum(durations.values()) - (n_cities - 1) == total_days

    # Backtracking to find an order of cities (each exactly once) that:
    # - respects direct flights between consecutive cities
    # - assigns block start days matching pinned constraints
    # - ends on Day 28
    best_path = None

    # Precompute a sorted order of cities to try for deterministic search
    base_order = sorted(cities)

    def backtrack(path, used, current_start):
        nonlocal best_path

        if len(path) == n_cities:
            # Verify end day equals total_days
            last_city = path[-1]
            end_day = current_start + durations[last_city] - 1
            if end_day == total_days:
                best_path = list(path)
            return

        # Determine the start day for the next city block
        if not path:
            next_start = 1
        else:
            last_city = path[-1]
            next_start = current_start + durations[last_city] - 1

        # If next_start equals any pinned start, enforce that city
        required_city = None
        for c, d in pinned_starts.items():
            if next_start == d:
                required_city = c
                break

        # Deadline prune: if we have already passed a pinned start without placing that city, prune
        for c, d in pinned_starts.items():
            if c not in used and (required_city != c):
                # If the pinned start day is strictly less than the next start day, we missed it
                if d < next_start:
                    return

        # Generate candidate cities
        if required_city:
            if required_city in used:
                return
            candidates = [required_city]
        else:
            candidates = [c for c in base_order if c not in used]

        # Try candidates
        for c in candidates:
            # Check the pinned condition: if c has a specific pinned start, enforce it
            if c in pinned_starts and pinned_starts[c] != next_start:
                continue

            # Adjacency check for direct flight from previous city to c
            if path:
                prev = path[-1]
                if prev not in edges or c not in edges[prev]:
                    continue

            # Proceed
            path.append(c)
            used.add(c)
            # Update current_start to the start day of the city we just placed
            backtrack(path, used, next_start)
            if best_path is not None:
                return
            used.remove(c)
            path.pop()

    # Start search (heuristic: try a reasonable initial city first to reduce branching)
    backtrack([], set(), 0)

    if best_path is None:
        raise RuntimeError("No feasible itinerary found under the given constraints.")

    # Build itinerary with day ranges
    itinerary = []
    start_day = 1
    for i, city in enumerate(best_path):
        end_day = start_day + durations[city] - 1
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
        start_day = end_day

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = find_itinerary()
    print(json.dumps(result, ensure_ascii=False))