import json
from typing import Dict, List, Tuple, Set, Optional

def build_adjacency(flights: List[Tuple[str, str]]) -> Dict[str, Set[str]]:
    adj = {}
    for a, b in flights:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    return adj

def compute_itinerary(
    total_days: int,
    city_durations: Dict[str, int],
    direct_flights: List[Tuple[str, str]],
    fixed_windows: Dict[str, Tuple[int, int]],
) -> Optional[List[Tuple[str, int, int]]]:
    """
    Returns a list of (city, start_day, end_day) covering all cities exactly once,
    with direct flights between consecutive cities, respecting fixed windows.
    """
    cities = list(city_durations.keys())
    n = len(cities)
    assert n == 9, "There must be exactly 9 cities."

    # Validate durations sum and link to total days via number of flights
    total_city_days = sum(city_durations.values())
    # In a path of 9 cities, there will be 8 flights; "double counting" adds flights
    expected_total_city_days = total_days + (n - 1)
    if total_city_days != expected_total_city_days:
        raise ValueError("Durations sum inconsistent with total_days and flights.")

    # Validate fixed windows durations match city durations
    for city, (a, b) in fixed_windows.items():
        dur = city_durations[city]
        if (b - a + 1) != dur:
            raise ValueError(f"Window for {city} does not match required duration.")

    adj = build_adjacency(direct_flights)

    # Precompute target start day for any city with a fixed window
    fixed_starts = {city: a for city, (a, b) in fixed_windows.items()}

    # Backtracking search
    best_order = []

    def backtrack(order: List[str], remaining: Set[str], prev_city: Optional[str], start_day: int) -> bool:
        nonlocal best_order

        # If a city has a fixed start equal to the current start_day, we must place it now
        must_place_now = [c for c in remaining if c in fixed_starts and fixed_starts[c] == start_day]
        if len(must_place_now) > 1:
            return False  # impossible to place more than one city at the same required start
        if len(must_place_now) == 1:
            candidates = must_place_now
        else:
            candidates = list(remaining)

        # Order candidates to improve pruning: prefer cities with windows earlier, then smaller degree
        def cand_key(c):
            win = fixed_starts.get(c, 10**9)
            degree = len(adj.get(c, []))
            return (win, degree)
        candidates.sort(key=cand_key)

        for city in candidates:
            # Adjacency check
            if prev_city is not None and city not in adj.get(prev_city, set()):
                continue

            # Window check for this city
            dur = city_durations[city]
            end_day = start_day + dur - 1
            if city in fixed_windows:
                a, b = fixed_windows[city]
                if not (start_day == a and end_day == b):
                    continue

            # Lookahead: after placing this city, next start_day becomes end_day (flight on end_day)
            next_start = end_day

            # Prune if any remaining city with a fixed start is now in the past
            for rc in remaining:
                if rc == city:
                    continue
                if rc in fixed_starts and fixed_starts[rc] < next_start:
                    break
            else:
                # Accept and recurse
                order.append(city)
                remaining.remove(city)

                if len(order) == n:
                    # Completed all cities; end_day must equal total_days by construction
                    best_order = order[:]
                    return True

                if backtrack(order, remaining, city, next_start):
                    return True

                # Undo
                remaining.add(city)
                order.pop()

        return False

    # Start search
    remaining = set(cities)
    if not backtrack([], remaining, None, 1):
        return None

    # Build day ranges from order
    itinerary = []
    start_day = 1
    for city in best_order:
        dur = city_durations[city]
        end_day = start_day + dur - 1
        itinerary.append((city, start_day, end_day))
        start_day = end_day  # flight day overlaps

    return itinerary

def main():
    total_days = 25

    # City durations (days present, counting flight days on transitions)
    city_durations = {
        "Salzburg": 2,
        "Hamburg": 4,
        "Venice": 5,
        "Nice": 3,
        "Zurich": 5,
        "Bucharest": 4,
        "Copenhagen": 4,
        "Brussels": 2,
        "Naples": 4,
    }

    # Direct flights (undirected)
    direct_flights = [
        ("Zurich", "Brussels"),
        ("Bucharest", "Copenhagen"),
        ("Venice", "Brussels"),
        ("Nice", "Zurich"),
        ("Hamburg", "Nice"),
        ("Zurich", "Naples"),
        ("Hamburg", "Bucharest"),
        ("Zurich", "Copenhagen"),
        ("Bucharest", "Brussels"),
        ("Hamburg", "Brussels"),
        ("Venice", "Naples"),
        ("Venice", "Copenhagen"),
        ("Bucharest", "Naples"),
        ("Hamburg", "Copenhagen"),
        ("Venice", "Zurich"),
        ("Nice", "Brussels"),
        ("Hamburg", "Venice"),
        ("Copenhagen", "Naples"),
        ("Nice", "Naples"),
        ("Hamburg", "Zurich"),
        ("Salzburg", "Hamburg"),
        ("Zurich", "Bucharest"),
        ("Brussels", "Naples"),
        ("Copenhagen", "Brussels"),
        ("Venice", "Nice"),
        ("Nice", "Copenhagen"),
    ]

    # Fixed windows (inclusive) inferred from constraints:
    fixed_windows = {
        "Nice": (9, 11),        # Visit relatives between day 9 and 11
        "Copenhagen": (18, 21), # Wedding between day 18 and 21
        "Brussels": (21, 22),   # Meet friends between day 21 and 22
        "Naples": (22, 25),     # Workshop between day 22 and 25
    }

    itinerary = compute_itinerary(total_days, city_durations, direct_flights, fixed_windows)
    if itinerary is None:
        print(json.dumps({"error": "No feasible itinerary found."}))
        return

    # Format output
    output = {
        "itinerary": [
            {
                "day_range": f"Day {start}-{end}",
                "place": city
            }
            for (city, start, end) in itinerary
        ]
    }
    print(json.dumps(output))

if __name__ == "__main__":
    main()