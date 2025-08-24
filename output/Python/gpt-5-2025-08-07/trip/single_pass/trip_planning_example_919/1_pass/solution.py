import json
from itertools import permutations

def build_adjacency():
    # Build directed adjacency from the provided direct-flight statements
    adj = {}
    def add(a, b):
        adj.setdefault(a, set()).add(b)
    def add_bidir(a, b):
        add(a, b)
        add(b, a)

    add_bidir("Riga", "Oslo")
    add_bidir("Rome", "Oslo")
    add_bidir("Vienna", "Milan")
    add_bidir("Vienna", "Vilnius")
    add_bidir("Vienna", "Lisbon")
    add_bidir("Riga", "Milan")
    add_bidir("Lisbon", "Oslo")
    add("Rome", "Riga")  # directed
    add_bidir("Rome", "Lisbon")
    add_bidir("Vienna", "Riga")
    add_bidir("Vienna", "Rome")
    add_bidir("Milan", "Oslo")
    add_bidir("Vienna", "Oslo")
    add_bidir("Vilnius", "Oslo")
    add("Riga", "Vilnius")  # directed
    add_bidir("Vilnius", "Milan")
    add_bidir("Riga", "Lisbon")
    add_bidir("Milan", "Lisbon")
    return adj

def compute_schedule(order, durations):
    # Given an ordered list of cities, compute inclusive day ranges with 1-day overlaps at transitions
    schedule = []
    start = 1
    for i, city in enumerate(order):
        length = durations[city]
        end = start + length - 1
        schedule.append((city, start, end))
        # Next city starts on the same day as current end (flight day counts for both)
        start = end
    return schedule

def satisfies_windows(schedule, city_windows):
    # Check that required windows [L, U] are included within each city's [start, end]
    start_end = {city: (s, e) for city, s, e in schedule}
    for city, (L, U) in city_windows.items():
        if city not in start_end:
            return False
        s, e = start_end[city]
        if not (s <= L and e >= U):
            return False
    return True

def satisfies_must_days(schedule, must_days):
    # Ensure specific days are covered by specific cities
    start_end = {city: (s, e) for city, s, e in schedule}
    for city, days in must_days.items():
        if city not in start_end:
            return False
        s, e = start_end[city]
        for d in days:
            if not (s <= d <= e):
                return False
    return True

def adjacency_ok(order, adj):
    # Ensure each consecutive pair has a direct flight (directed)
    for a, b in zip(order, order[1:]):
        if b not in adj.get(a, set()):
            return False
    return True

def backtrack_find_itinerary(cities, durations, total_days, adj, city_windows, must_days):
    # We enforce Vienna to be first (must be in Vienna on Day 1) and unique visit to each city
    start_city = "Vienna"
    others = [c for c in cities if c != start_city]

    # Try all permutations for the remaining cities
    for perm in permutations(others):
        order = [start_city] + list(perm)

        # Quick adjacency check
        if not adjacency_ok(order, adj):
            continue

        # Compute schedule
        schedule = compute_schedule(order, durations)

        # Check total trip end day equals total_days
        final_end = schedule[-1][2]
        if final_end != total_days:
            continue

        # Windows (Lisbon between 11 and 13 inclusive, Oslo between 13 and 15 inclusive)
        if not satisfies_windows(schedule, city_windows):
            continue

        # Must days for Vienna (day 1 and day 4)
        if not satisfies_must_days(schedule, must_days):
            continue

        # All constraints satisfied
        return schedule

    return None

def main():
    # Input variables (trip constraints)
    total_days = 15
    cities = ["Vienna", "Milan", "Rome", "Riga", "Lisbon", "Vilnius", "Oslo"]
    durations = {
        "Vienna": 4,
        "Milan": 2,
        "Rome": 3,
        "Riga": 2,
        "Lisbon": 3,
        "Vilnius": 4,
        "Oslo": 3,
    }
    # Day-specific constraints
    must_days = {
        "Vienna": {1, 4}
    }
    # Interval windows (inclusive)
    city_windows = {
        "Lisbon": (11, 13),  # visit relatives in Lisbon between day 11 and 13
        "Oslo": (13, 15),    # meet a friend in Oslo between day 13 and 15
    }

    adj = build_adjacency()

    schedule = backtrack_find_itinerary(cities, durations, total_days, adj, city_windows, must_days)

    itinerary = []
    if schedule:
        for city, start, end in schedule:
            itinerary.append({
                "day_range": f"Day {start}-{end}",
                "place": city
            })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()