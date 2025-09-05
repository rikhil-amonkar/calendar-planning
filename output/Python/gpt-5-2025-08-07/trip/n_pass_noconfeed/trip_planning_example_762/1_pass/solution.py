import itertools
import json

def main():
    # Input variables based on the problem statement
    total_days = 13
    cities_required_days = {
        "Dublin": 3,
        "Madrid": 2,
        "Oslo": 3,
        "London": 2,
        "Vilnius": 3,
        "Berlin": 5,
    }

    # Constraints
    constraints = {
        # Must be in Madrid on Day 2 and Day 3 (visiting relatives)
        "must_cover_days": {
            "Madrid": {2, 3},
        },
        # Dublin's 3-day stay should be between Day 7 and Day 9 (meeting friends)
        "must_be_within_range": {
            "Dublin": (7, 9),
        },
        # Must attend wedding in Berlin on at least one day between Day 3 and Day 7
        "must_include_any_day_in_range": {
            "Berlin": (3, 7),
        },
    }

    # Direct flights (undirected)
    direct_flights_pairs = [
        ("London", "Madrid"),
        ("Oslo", "Vilnius"),
        ("Berlin", "Vilnius"),
        ("Madrid", "Oslo"),
        ("Madrid", "Dublin"),
        ("London", "Oslo"),
        ("Madrid", "Berlin"),
        ("Berlin", "Oslo"),
        ("Dublin", "Oslo"),
        ("London", "Dublin"),
        ("London", "Berlin"),
        ("Berlin", "Dublin"),
    ]

    # Build undirected adjacency set
    direct = set()
    for a, b in direct_flights_pairs:
        direct.add((a, b))
        direct.add((b, a))

    cities = list(cities_required_days.keys())

    def compute_schedule(order):
        """Given an order of cities, compute (start, end) for each city using
        overlapping travel on transition days."""
        schedule = {}
        end_prev = None
        for i, city in enumerate(order):
            duration = cities_required_days[city]
            if end_prev is None:
                start = 1
            else:
                start = end_prev  # travel day counts for both cities
            end = start + duration - 1
            schedule[city] = (start, end)
            end_prev = end
        return schedule

    def adjacency_ok(order):
        for i in range(len(order) - 1):
            if (order[i], order[i + 1]) not in direct:
                return False
        return True

    def satisfies_constraints(schedule):
        # End day must match total_days
        last_end = max(e for (_, e) in schedule.values())
        first_start = min(s for (s, _) in schedule.values())
        if first_start != 1 or last_end != total_days:
            return False

        # Must cover specific days in city
        for city, required_days in constraints.get("must_cover_days", {}).items():
            s, e = schedule[city]
            city_days = set(range(s, e + 1))
            if not required_days.issubset(city_days):
                return False

        # City's entire range must fall within a window
        for city, (a, b) in constraints.get("must_be_within_range", {}).items():
            s, e = schedule[city]
            if not (s >= a and e <= b):
                return False

        # City must include at least one day within a window
        for city, (a, b) in constraints.get("must_include_any_day_in_range", {}).items():
            s, e = schedule[city]
            if e < a or s > b:
                return False

        # Validate city-day totals match requirements
        for city, (s, e) in schedule.items():
            if (e - s + 1) != cities_required_days[city]:
                return False

        return True

    # Search for a valid order that satisfies adjacency and all constraints
    valid_schedule = None
    # For determinism, iterate permutations in a consistent order
    for order in itertools.permutations(sorted(cities)):
        # Quick pruning: sum durations = total_days + (n-1) must hold, ensured by inputs
        # Check adjacency first for speed
        if not adjacency_ok(order):
            continue
        schedule = compute_schedule(order)
        if satisfies_constraints(schedule):
            valid_schedule = (order, schedule)
            break

    if not valid_schedule:
        print(json.dumps({"error": "No valid itinerary found with the given constraints."}))
        return

    order, schedule = valid_schedule

    # Build itinerary in chronological order
    segments = sorted(((s, e, city) for city, (s, e) in schedule.items()), key=lambda x: (x[0], x[1]))
    itinerary = []
    for s, e, city in segments:
        itinerary.append({"day_range": f"Day {s}-{e}", "place": city})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()