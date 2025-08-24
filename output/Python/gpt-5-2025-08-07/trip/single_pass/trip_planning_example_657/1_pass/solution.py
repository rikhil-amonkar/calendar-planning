import json
from itertools import permutations

def plan_trip():
    # Input variables (constraints)
    total_days = 16
    required_days = {
        "Frankfurt": 4,
        "Manchester": 4,
        "Valencia": 4,
        "Naples": 4,
        "Oslo": 3,
        "Vilnius": 2,
    }
    show_city = "Frankfurt"
    show_start = 13
    show_end = 16
    wedding_city = "Vilnius"
    wedding_start = 12
    wedding_end = 13

    # Direct flight connections (undirected)
    direct_pairs = [
        ("Valencia", "Frankfurt"),
        ("Manchester", "Frankfurt"),
        ("Naples", "Manchester"),
        ("Naples", "Frankfurt"),
        ("Naples", "Oslo"),
        ("Oslo", "Frankfurt"),
        ("Vilnius", "Frankfurt"),
        ("Oslo", "Vilnius"),
        ("Manchester", "Oslo"),
        ("Valencia", "Naples"),
    ]

    # Build adjacency map
    adj = {}
    def add_edge(a, b):
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    for a, b in direct_pairs:
        add_edge(a, b)

    cities = list(required_days.keys())

    # Derived calculations
    sum_required = sum(required_days.values())
    min_flights_needed = sum_required - total_days  # leveraging overlap rule
    # With 6 cities, the minimal number of flights if visiting each exactly once is 5
    # This must equal min_flights_needed for an optimal plan
    if min_flights_needed != len(cities) - 1:
        raise ValueError("Constraints inconsistent with optimal single-visit chain (flights mismatch).")

    # We must be in Frankfurt on days 13-16; enforce Frankfurt as last city in the chain
    last_city = show_city
    # Wedding around day 12-13; enforce Vilnius immediately before Frankfurt to use Day 12 (arrival) and Day 13 (departure)
    penultimate_city = wedding_city

    # Remaining cities to order before Vilnius
    pre_chain_cities = [c for c in cities if c not in {penultimate_city, last_city}]

    # Try to find a valid path C1 -> C2 -> C3 -> C4 -> Vilnius -> Frankfurt using only direct flights
    path = None
    for perm in permutations(pre_chain_cities):
        candidate = list(perm) + [penultimate_city, last_city]
        ok = True
        for i in range(len(candidate) - 1):
            a, b = candidate[i], candidate[i + 1]
            if b not in adj.get(a, set()):
                ok = False
                break
        if ok:
            path = candidate
            break

    if path is None:
        raise ValueError("No valid chain of direct flights found meeting ordering constraints.")

    # Build the day-by-day schedule using overlap on flight days:
    # Strategy:
    # - First city: spend (req-1) pure days, then fly to next city on a flight day (counts for both)
    # - Intermediate cities (except last): after flight-in day, spend (req-2) pure days, then next flight day
    # - Last city: after flight-in day, spend (req-1) pure days (no further flights)
    days = {d: [] for d in range(1, total_days + 1)}
    flights = []  # list of tuples (day, from_city, to_city)

    day = 1
    # First city pure days
    first_city = path[0]
    pure_first = required_days[first_city] - 1
    if pure_first < 0:
        raise ValueError("Invalid required days for the first city.")
    for _ in range(pure_first):
        if day > total_days:
            raise ValueError("Schedule overflow before completing.")
        days[day].append(first_city)
        day += 1

    for i in range(len(path) - 1):
        a = path[i]
        b = path[i + 1]

        # Flight day a -> b (counts towards both)
        if day > total_days:
            raise ValueError("Schedule overflow on flight day.")
        days[day].extend([a, b])
        flights.append((day, a, b))
        day += 1

        # Post-flight pure days in city b
        if i + 1 == len(path) - 1:
            pure = required_days[b] - 1
        else:
            pure = required_days[b] - 2
        if pure < 0:
            raise ValueError("Invalid required days for intermediate city.")
        for _ in range(pure):
            if day > total_days:
                raise ValueError("Schedule overflow within city stay.")
            days[day].append(b)
            day += 1

    if day != total_days + 1:
        raise ValueError("Schedule does not exactly fill the total days.")

    # Validate per-city counts
    counts = {c: 0 for c in cities}
    for d in range(1, total_days + 1):
        for c in days[d]:
            counts[c] += 1
    for c in cities:
        if counts[c] != required_days[c]:
            raise ValueError(f"City {c} has {counts[c]} days, expected {required_days[c]}.")

    # Validate flights count equals min flights needed
    if len(flights) != min_flights_needed:
        raise ValueError("Number of flights does not match minimal required overlaps.")

    # Validate show presence
    for d in range(show_start, show_end + 1):
        if show_city not in days[d]:
            raise ValueError(f"Show-day presence violated on Day {d} in {show_city}.")

    # Validate wedding presence
    for d in range(wedding_start, wedding_end + 1):
        if wedding_city not in days[d]:
            raise ValueError(f"Wedding-day presence violated on Day {d} in {wedding_city}.")

    # Validate that all flights are along direct routes
    for d, a, b in flights:
        if b not in adj.get(a, set()):
            raise ValueError(f"Flight on Day {d} from {a} to {b} is not direct.")

    # Build JSON itinerary (day-by-day)
    flight_by_day = {d: (a, b) for d, a, b in flights}
    itinerary = []
    for d in range(1, total_days + 1):
        present = list(dict.fromkeys(days[d]))  # preserve order, dedupe
        if len(present) == 2 and d in flight_by_day:
            a, b = flight_by_day[d]
            place = f"{a} -> {b} (flight day)"
        elif len(present) == 1:
            place = present[0]
        else:
            # Fallback: join, though this shouldn't happen with the constructed schedule
            place = " & ".join(present)
        itinerary.append({"day_range": f"Day {d}", "place": place})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = plan_trip()
    print(json.dumps(result, ensure_ascii=False))