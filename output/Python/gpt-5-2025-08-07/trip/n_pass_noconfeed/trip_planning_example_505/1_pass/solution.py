import itertools
import json

def find_itinerary():
    # Input variables (trip constraints)
    total_days = 8
    cities = ["Prague", "Stuttgart", "Split", "Krakow", "Florence"]
    desired_durations = {
        "Prague": 4,
        "Stuttgart": 2,
        "Split": 2,
        "Krakow": 2,
        "Florence": 2,
    }
    # Direct flight routes (undirected)
    direct_routes = {
        frozenset(("Stuttgart", "Split")),
        frozenset(("Prague", "Florence")),
        frozenset(("Krakow", "Stuttgart")),
        frozenset(("Krakow", "Split")),
        frozenset(("Split", "Prague")),
        frozenset(("Krakow", "Prague")),
    }
    # Boundary constraints: must be in city at boundary (day d and day d+1)
    boundary_requirements = {
        (2, 3): "Stuttgart",
        (3, 4): "Split",
    }

    # Helper to check a path uses only direct flights between consecutive cities
    def path_has_only_direct_flights(path):
        for i in range(len(path) - 1):
            if frozenset((path[i], path[i+1])) not in direct_routes:
                return False
        return True

    # Build per-day sets of cities given a path and specific flight days
    # flight_days is a sorted tuple of 4 distinct integers in [1..8]
    def build_timeline(path, flight_days):
        # Timeline: day -> set of cities present on that day
        day_cities = {d: set() for d in range(1, total_days + 1)}
        current_index = 0  # index into path; start in path[0]
        # Map flight days to edges in order: day flight_days[k] flies from path[k] to path[k+1]
        for day in range(1, total_days + 1):
            # Always present in current city
            day_cities[day].add(path[current_index])
            # If this day is a flight day, add destination city too and advance current city
            if day in flight_days:
                # Determine which edge index this is
                k = flight_days.index(day)  # 0..3
                src = path[k]
                dst = path[k+1]
                # Ensure our current position matches src (sanity)
                if path[current_index] != src:
                    return None  # inconsistent schedule
                day_cities[day].add(dst)
                current_index += 1  # move to next city for subsequent days

        # After the loop, we should have completed exactly len(path)-1 moves
        if current_index != len(path) - 1:
            return None

        return day_cities

    # Count days per city (including overlapping flight days)
    def count_days_per_city(day_cities):
        counts = {c: 0 for c in cities}
        for d in range(1, total_days + 1):
            for c in day_cities[d]:
                counts[c] += 1
        return counts

    # Check boundary requirements: city must be present on both days at the boundary
    def boundaries_satisfied(day_cities):
        for (d1, d2), city in boundary_requirements.items():
            if city not in day_cities[d1] or city not in day_cities[d2]:
                return False
        return True

    # Feasibility check that supports durations and boundaries
    def is_feasible(path, flight_days):
        # Day 3 must be the Stuttgart->Split flight (to be in both cities on day 3)
        # This implies Stuttgart and Split are adjacent as path[i], path[i+1] and flight_days[i] == 3
        try:
            i_stu = path.index("Stuttgart")
            if i_stu == len(path) - 1 or path[i_stu + 1] != "Split":
                return False  # must be adjacent and in this order
            # Ensure day 3 is the flight for this edge
            if len(flight_days) < i_stu + 1 or flight_days[i_stu] != 3:
                return False
        except ValueError:
            return False

        # Build timeline and validate
        day_cities = build_timeline(path, flight_days)
        if day_cities is None:
            return False

        # Ensure only direct flights were used (redundant due to path check, but kept for clarity)
        if not path_has_only_direct_flights(path):
            return False

        # Durations must match exactly
        counts = count_days_per_city(day_cities)
        if counts != desired_durations:
            return False

        # Boundaries must be satisfied
        if not boundaries_satisfied(day_cities):
            return False

        return True

    # Once feasible, build itinerary (contiguous day ranges for each city)
    def build_itinerary(path, flight_days):
        day_cities = build_timeline(path, flight_days)
        # For each city, find contiguous range (in this path-based model, it's contiguous)
        city_days = {c: [] for c in cities}
        for day in range(1, total_days + 1):
            for c in day_cities[day]:
                city_days[c].append(day)
        ranges = []
        # Only include cities with non-zero days, sorted by first day present
        entries = []
        for c, days in city_days.items():
            if days:
                entries.append((min(days), max(days), c))
        entries.sort(key=lambda x: x[0])  # sort by start day

        itinerary = []
        for start, end, c in entries:
            itinerary.append({"day_range": f"Day {start}-{end}", "place": c})
        return itinerary

    # Generate all valid paths (permutations) and flight day schedules
    # Optimization: require that "Stuttgart" is immediately followed by "Split" in the path
    # and that the path uses only direct flights.
    valid_solution = None
    for path in itertools.permutations(cities):
        # Stuttgart must be immediately followed by Split
        try:
            idx_stu = path.index("Stuttgart")
            if idx_stu == len(path) - 1 or path[idx_stu + 1] != "Split":
                continue
        except ValueError:
            continue
        if not path_has_only_direct_flights(path):
            continue

        # Choose 4 flight days out of 8; ensure the (idx_stu)-th flight day (0-based) is exactly day 3
        # I.e., flight_days[idx_stu] == 3
        # We'll enumerate combinations and filter accordingly
        all_combos = itertools.combinations(range(1, total_days + 1), len(path) - 1)
        for combo in all_combos:
            if combo[idx_stu] != 3:
                continue
            # Build feasibility
            if is_feasible(path, combo):
                itinerary = build_itinerary(path, combo)
                valid_solution = {"itinerary": itinerary}
                break
        if valid_solution:
            break

    # If no valid solution was found (should not happen with given constraints), fallback gracefully
    if not valid_solution:
        # Though problem guarantees feasibility, return empty structure if not found
        valid_solution = {"itinerary": []}

    return valid_solution


if __name__ == "__main__":
    result = find_itinerary()
    print(json.dumps(result))