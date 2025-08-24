import itertools
import json

def build_adjacency(edges):
    adj = {}
    for a, b in edges:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    return adj

def has_direct(adj, a, b):
    return b in adj.get(a, set())

def compute_day_ranges(order, durations):
    # Sequential segments with 1-day overlaps: next_start = prev_end
    # Day counting inclusive
    ranges = []
    current_start = 1
    for city in order:
        end_day = current_start + durations[city] - 1
        ranges.append((city, current_start, end_day))
        current_start = end_day  # overlap next start with this end
    return ranges

def covers_window(rng_by_city, city, window):
    if city not in rng_by_city:
        return False
    s, e = rng_by_city[city]
    a, b = window
    return s <= a and e >= b

def main():
    # Input variables (constraints)
    total_days = 22
    durations = {
        "Valencia": 5,
        "Riga": 5,
        "Prague": 3,
        "Mykonos": 3,
        "Zurich": 5,
        "Bucharest": 5,
        "Nice": 2,
    }
    direct_flights = [
        ("Mykonos", "Nice"),
        ("Mykonos", "Zurich"),
        ("Prague", "Bucharest"),
        ("Valencia", "Bucharest"),
        ("Zurich", "Prague"),
        ("Riga", "Nice"),
        ("Zurich", "Riga"),
        ("Zurich", "Bucharest"),
        ("Zurich", "Valencia"),
        ("Bucharest", "Riga"),
        ("Prague", "Riga"),
        ("Prague", "Valencia"),
        ("Zurich", "Nice"),
    ]
    # Must include windows
    windows = {
        "Mykonos": (1, 3),  # wedding between day 1 and 3
        "Prague": (7, 9),   # relatives between day 7 and 9
    }

    # Sanity checks
    n_cities = len(durations)
    total_required = sum(durations.values())
    expected_total_days = total_required - (n_cities - 1)  # due to overlaps on flight days
    if expected_total_days != total_days:
        # If constraints don't compose to the total days, we cannot proceed
        raise ValueError("Given durations and overlaps cannot compose to the total days.")

    adj = build_adjacency(direct_flights)

    # We must start in a city that includes day 1 within its window.
    # Only Mykonos needs to include day 1-3; so we anchor the start at Mykonos.
    start_city = "Mykonos"
    other_cities = sorted([c for c in durations if c != start_city])

    best_itinerary = None

    # Generate all possible orders of remaining cities and test feasibility
    for perm in itertools.permutations(other_cities):
        order = [start_city] + list(perm)

        # Check adjacency (direct flights only)
        ok = True
        for a, b in zip(order[:-1], order[1:]):
            if not has_direct(adj, a, b):
                ok = False
                break
        if not ok:
            continue

        # Compute day ranges with 1-day overlaps
        ranges = compute_day_ranges(order, durations)
        # Build lookup by city
        rng_by_city = {city: (s, e) for city, s, e in ranges}

        # Validate windows
        if not all(covers_window(rng_by_city, city, win) for city, win in windows.items()):
            continue

        # Ensure the trip spans exactly total_days
        if ranges[-1][2] != total_days:
            continue

        # Found a valid itinerary (choose the first that satisfies constraints)
        best_itinerary = [{"day_range": f"Day {s}-{e}", "place": city} for city, s, e in ranges]
        break

    if not best_itinerary:
        raise RuntimeError("No feasible itinerary found with the given constraints and direct flights.")

    print(json.dumps({"itinerary": best_itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()