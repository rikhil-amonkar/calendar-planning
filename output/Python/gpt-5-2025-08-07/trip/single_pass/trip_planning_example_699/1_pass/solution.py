import itertools
import json

def main():
    # Input variables
    total_days = 16
    cities = ["Mykonos", "Reykjavik", "Dublin", "London", "Helsinki", "Hamburg"]
    desired_stays = {
        "Mykonos": 3,
        "Reykjavik": 2,
        "Dublin": 5,
        "London": 5,
        "Helsinki": 4,
        "Hamburg": 2,
    }
    # Direct flights (undirected)
    direct_flights_pairs = [
        ("Dublin", "London"),
        ("Hamburg", "Dublin"),
        ("Helsinki", "Reykjavik"),
        ("Hamburg", "London"),
        ("Dublin", "Helsinki"),
        ("Reykjavik", "London"),
        ("London", "Mykonos"),
        ("Dublin", "Reykjavik"),
        ("Hamburg", "Helsinki"),
        ("Helsinki", "London"),
    ]
    flights_set = set(frozenset(p) for p in direct_flights_pairs)

    # Time-sensitive constraints
    # Must cover all days in the interval (inclusive)
    must_cover_intervals = {
        "Dublin": (2, 6),  # Attend the show the entire period
    }
    # Must be present on each of these exact days
    must_be_on_days = {
        "Reykjavik": {9, 10},  # Wedding coverage
    }
    # Must be present at least one day within this interval
    at_least_one_in_interval = {
        "Hamburg": (1, 2),  # Meet friends on Day 1 or Day 2
    }

    # Helper functions
    def is_direct_path(order):
        return all(frozenset((order[i], order[i+1])) in flights_set for i in range(len(order)-1))

    def compute_ranges(order):
        # With overlaps on flight days: next city starts on the last day of the previous city's range
        day_start = 1
        ranges = {}
        for city in order:
            d = desired_stays[city]
            day_end = day_start + d - 1
            ranges[city] = (day_start, day_end)
            day_start = day_end  # overlap with next city on this boundary day
        return ranges

    def covers_interval(rng, start, end):
        return rng[0] <= start and rng[1] >= end

    def contains_day(rng, day):
        return rng[0] <= day <= rng[1]

    # Basic feasibility check: sum of stays must equal total_days + number_of_flights (which is n-1)
    n = len(cities)
    sum_stays = sum(desired_stays[c] for c in cities)
    required_total_days = sum_stays - (n - 1)
    if required_total_days != total_days:
        # Infeasible by arithmetic constraint
        print(json.dumps({"itinerary": [], "note": "No feasible itinerary matches total days with given stays."}))
        return

    best_order = None
    best_ranges = None

    # Try all permutations that respect direct flights between consecutive cities
    for order in itertools.permutations(cities):
        if not is_direct_path(order):
            continue
        ranges = compute_ranges(order)
        # Check the final day matches the trip length
        last_city = order[-1]
        if ranges[last_city][1] != total_days:
            continue

        # Check must-cover intervals (e.g., Dublin show)
        ok = True
        for city, (s, e) in must_cover_intervals.items():
            if city not in ranges or not covers_interval(ranges[city], s, e):
                ok = False
                break
        if not ok:
            continue

        # Check must-be-on-days (e.g., Reykjavik wedding)
        for city, days in must_be_on_days.items():
            if city not in ranges or not all(contains_day(ranges[city], d) for d in days):
                ok = False
                break
        if not ok:
            continue

        # Check at-least-one-in-interval (e.g., Hamburg meet friends Day 1-2)
        for city, (s, e) in at_least_one_in_interval.items():
            if city not in ranges or not any(contains_day(ranges[city], d) for d in range(s, e + 1)):
                ok = False
                break
        if not ok:
            continue

        # Found a valid itinerary; choose the first valid (or could score/optimize further)
        best_order = order
        best_ranges = ranges
        break

    if best_order is None:
        print(json.dumps({"itinerary": [], "note": "No feasible itinerary found under given constraints."}))
        return

    # Build the output itinerary in order
    itinerary = []
    for city in best_order:
        s, e = best_ranges[city]
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))


if __name__ == "__main__":
    main()