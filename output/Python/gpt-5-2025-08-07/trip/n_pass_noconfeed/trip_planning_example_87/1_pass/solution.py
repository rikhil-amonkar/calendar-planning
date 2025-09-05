import json
from itertools import permutations, product

def build_adjacency(direct_flights):
    adj = {}
    for a, b in direct_flights:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    return adj

def simple_paths_covering_cities(start_city, cities, adj):
    # Generate all simple paths that start at start_city and visit every city exactly once
    others = [c for c in cities if c != start_city]
    for perm in permutations(others):
        path = (start_city,) + perm
        # Check consecutive legs are direct
        valid = True
        for i in range(len(path) - 1):
            if path[i+1] not in adj.get(path[i], set()):
                valid = False
                break
        if valid:
            yield path

def compute_schedule_for_path(path, total_days, required_stays):
    # For 3 cities, denote path = (C1, C2, C3)
    C1, C2, C3 = path
    # From overlap rules:
    # days in C3 = total_days - t2 + 1 => t2 = total_days - req[C3] + 1
    t2 = total_days - required_stays[C3] + 1
    # days in C2 = t2 - t1 + 1 => t1 = t2 - req[C2] + 1
    t1 = t2 - required_stays[C2] + 1
    # days in C1 will be t1 (since days 1..t1 inclusive)
    # Validate boundaries
    if not (1 <= t1 <= t2 <= total_days):
        return None, None, None
    # Build daily occupancy per the overlap rule
    occupancy = []
    for d in range(1, total_days + 1):
        here = set()
        if d <= t1:
            here.add(C1)
        if t1 <= d <= t2:
            here.add(C2)
        if d >= t2:
            here.add(C3)
        occupancy.append(here)
    # Validate counts
    counts = {city: 0 for city in [C1, C2, C3]}
    for dset in occupancy:
        for city in dset:
            counts[city] += 1
    for city, req in required_stays.items():
        if counts.get(city, 0) != req:
            return None, None, None
    return t1, t2, occupancy

def satisfies_must_days(occupancy, must_be_in_city_days):
    # must_be_in_city_days: dict city -> iterable of day numbers that must include the city
    for city, days in must_be_in_city_days.items():
        for d in days:
            if d < 1 or d > len(occupancy):
                return False
            if city not in occupancy[d - 1]:
                return False
    return True

def choose_optimal_plan(total_days, cities, direct_flights, required_stays, must_be_in_city_days):
    adj = build_adjacency(direct_flights)

    # Determine start city: the city that must include Day 1 if specified, otherwise first in list
    start_city = None
    for city, days in must_be_in_city_days.items():
        if 1 in set(days):
            start_city = city
            break
    if start_city is None:
        start_city = cities[0]

    best = None
    # Generate feasible paths
    for path in simple_paths_covering_cities(start_city, cities, adj):
        # Compute schedule for this path
        t1, t2, occupancy = compute_schedule_for_path(path, total_days, required_stays)
        if occupancy is None:
            continue
        # Validate must days
        if not satisfies_must_days(occupancy, must_be_in_city_days):
            continue
        # Objective: minimize number of flight days (always len(path)-1), then earliest departures
        # Here, we'll prefer earliest t1, then earliest t2
        key = (t1, t2)
        if best is None or key < best["key"]:
            best = {
                "path": path,
                "t1": t1,
                "t2": t2,
                "occupancy": occupancy,
                "key": key
            }
    return best

def build_itinerary_from_plan(plan, total_days):
    C1, C2, C3 = plan["path"]
    t1, t2 = plan["t1"], plan["t2"]
    itinerary = [
        {"day_range": f"Day 1-{t1}", "place": C1},
        {"day_range": f"Day {t1}-{t2}", "place": C2},
        {"day_range": f"Day {t2}-{total_days}", "place": C3},
    ]
    return itinerary

def main():
    # Input variables (trip constraints)
    total_days = 7
    cities = ["Riga", "Amsterdam", "Mykonos"]
    direct_flights = [
        ("Amsterdam", "Mykonos"),
        ("Riga", "Amsterdam"),
    ]
    required_stays = {
        "Riga": 2,
        "Amsterdam": 2,
        "Mykonos": 5,
    }
    must_be_in_city_days = {
        # Must be in Riga on days 1 and 2 (to visit relatives between day 1 and day 2)
        "Riga": [1, 2]
    }

    # Compute optimal itinerary
    plan = choose_optimal_plan(total_days, cities, direct_flights, required_stays, must_be_in_city_days)

    if plan is None:
        output = {"itinerary": []}
    else:
        itinerary = build_itinerary_from_plan(plan, total_days)
        output = {"itinerary": itinerary}

    print(json.dumps(output))

if __name__ == "__main__":
    main()