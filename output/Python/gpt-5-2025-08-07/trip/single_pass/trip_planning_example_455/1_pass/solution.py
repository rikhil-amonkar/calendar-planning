import json
import itertools

def compute_itinerary():
    # Input variables (trip constraints)
    total_days = 21
    cities = ["Reykjavik", "Riga", "Warsaw", "Istanbul", "Krakow"]
    durations = {
        "Reykjavik": 7,
        "Riga": 2,
        "Warsaw": 3,
        "Istanbul": 6,
        "Krakow": 7,
    }
    # Direct flights (undirected)
    direct_flights = {
        frozenset(["Istanbul", "Krakow"]),
        frozenset(["Warsaw", "Reykjavik"]),
        frozenset(["Istanbul", "Warsaw"]),
        frozenset(["Riga", "Istanbul"]),
        frozenset(["Krakow", "Warsaw"]),
        frozenset(["Riga", "Warsaw"]),
    }
    # Special constraints
    meet_friend_city = "Riga"
    meet_friend_window = (1, 2)  # inclusive range
    wedding_city = "Istanbul"
    wedding_window = (2, 7)      # inclusive range

    def has_direct(a, b):
        return frozenset([a, b]) in direct_flights

    def build_schedule(order):
        # Build overlapped day ranges:
        # Each city i has an inclusive range [start, end],
        # Next city starts on 'end' to model travel day counting in both cities.
        ranges = {}
        current_start = 1
        for idx, city in enumerate(order):
            start = current_start
            end = start + durations[city] - 1
            ranges[city] = (start, end)
            if idx < len(order) - 1:
                current_start = end  # overlap next start on this end (travel day)
        return ranges

    def expand_days(rng):
        return set(range(rng[0], rng[1] + 1))

    def validate(order, ranges):
        # Check direct flights between consecutive cities
        for a, b in zip(order, order[1:]):
            if not has_direct(a, b):
                return False

        # Check total calendar days equals total_days
        last_city = order[-1]
        if ranges[last_city][1] != total_days:
            return False

        # Check each city's day count matches requested duration
        for city in order:
            if len(expand_days(ranges[city])) != durations[city]:
                return False

        # Friend in Riga between day 1 and day 2
        riga_days = expand_days(ranges[meet_friend_city])
        if len(riga_days.intersection(set(range(meet_friend_window[0], meet_friend_window[1] + 1)))) == 0:
            return False

        # Wedding in Istanbul between day 2 and 7
        ist_days = expand_days(ranges[wedding_city])
        if len(ist_days.intersection(set(range(wedding_window[0], wedding_window[1] + 1)))) == 0:
            return False

        return True

    # Objective: find an order that satisfies constraints using direct flights only.
    # Primary goal: satisfy all constraints.
    # Secondary goal: earliest possible start day in Istanbul within the valid set.
    best = None
    best_score = None

    for order in itertools.permutations(cities):
        # Quick feasibility pruning:
        # - Reykjavik only connects to Warsaw, so it must be adjacent to Warsaw in the path.
        # - To meet the friend window (day 1-2) with 2 days in Riga, Riga must be the first city.
        if order[0] != "Riga":
            continue
        # Reykjavik must be adjacent to Warsaw in the path
        idx_rey = order.index("Reykjavik")
        neighbors = []
        if idx_rey > 0:
            neighbors.append(order[idx_rey - 1])
        if idx_rey < len(order) - 1:
            neighbors.append(order[idx_rey + 1])
        if "Warsaw" not in neighbors:
            continue

        # Check direct flights adjacency; skip early if any missing
        if any(not has_direct(a, b) for a, b in zip(order, order[1:])):
            continue

        # Build ranges and validate
        ranges = build_schedule(order)
        if not validate(order, ranges):
            continue

        # Scoring: earliest Istanbul start day preferred
        ist_start = ranges["Istanbul"][0]
        score = (ist_start, )

        if best is None or score < best_score:
            best = (order, ranges)
            best_score = score

    # If no solution found, return empty itinerary (should not happen with given constraints)
    if best is None:
        return {"itinerary": []}

    order, ranges = best
    itinerary = []
    for city in order:
        start, end = ranges[city]
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result, ensure_ascii=False))