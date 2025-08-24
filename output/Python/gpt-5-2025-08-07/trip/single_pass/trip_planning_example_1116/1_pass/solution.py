import itertools
import json

def build_graph(flight_pairs):
    g = {}
    for a, b in flight_pairs:
        g.setdefault(a, set()).add(b)
        g.setdefault(b, set()).add(a)
    return g

def compute_day_ranges(order, durations, start_day=1):
    ranges = {}
    s = start_day
    for city in order:
        e = s + durations[city] - 1
        ranges[city] = (s, e)
        s = e  # next segment overlaps on the end day (flight day)
    # After the last city, the calendar end day equals start + sum(durations) - (n-1) - 1
    return ranges

def range_includes_days(rng, days):
    s, e = rng
    return all(s <= d <= e for d in days)

def range_intersects(rng, window):
    s, e = rng
    ws, we = window
    return not (e < ws or s > we)

def is_path_with_direct_flights(order, graph):
    return all(order[i+1] in graph.get(order[i], set()) for i in range(len(order)-1))

def find_itinerary():
    total_days = 20

    # Input variables (constraints)
    cities = [
        "Oslo",
        "Reykjavik",
        "Stockholm",
        "Munich",
        "Frankfurt",
        "Barcelona",
        "Bucharest",
        "Split",
    ]

    durations = {
        "Oslo": 2,
        "Reykjavik": 5,
        "Stockholm": 4,
        "Munich": 4,
        "Frankfurt": 4,
        "Barcelona": 3,
        "Bucharest": 2,
        "Split": 3,
    }

    # Flight connectivity (direct flights only)
    flight_pairs = [
        ("Reykjavik", "Munich"),
        ("Munich", "Frankfurt"),
        ("Split", "Oslo"),
        ("Reykjavik", "Oslo"),
        ("Bucharest", "Munich"),
        ("Oslo", "Frankfurt"),
        ("Bucharest", "Barcelona"),
        ("Barcelona", "Frankfurt"),
        ("Reykjavik", "Frankfurt"),
        ("Barcelona", "Stockholm"),
        ("Barcelona", "Reykjavik"),
        ("Stockholm", "Reykjavik"),
        ("Barcelona", "Split"),
        ("Bucharest", "Oslo"),
        ("Bucharest", "Frankfurt"),
        ("Split", "Stockholm"),
        ("Barcelona", "Oslo"),
        ("Stockholm", "Munich"),
        ("Stockholm", "Oslo"),
        ("Split", "Frankfurt"),
        ("Barcelona", "Munich"),
        ("Stockholm", "Frankfurt"),
        ("Munich", "Oslo"),
        ("Split", "Munich"),
    ]

    # Time window constraints
    # - If "must_include_days": all listed days must fall within the city's inclusive range.
    # - If "must_intersect": the city's range must intersect this inclusive window.
    windows = {
        "Oslo": {"must_include_days": [16, 17]},
        "Reykjavik": {"must_intersect": (9, 13)},   # meet friend in Reykjavik between day 9 and 13
        "Munich": {"must_intersect": (13, 16)},     # visit relatives between day 13 and 16
        "Frankfurt": {"must_intersect": (17, 20)},  # workshop between day 17 and 20
    }

    # Basic validations
    assert set(cities) == set(durations.keys())
    assert sum(durations.values()) == total_days + (len(cities) - 1)  # 27 = 20 + 7

    graph = build_graph(flight_pairs)

    best_order = None
    best_ranges = None

    # Search all permutations for a valid order that satisfies:
    # - direct flights between consecutive cities
    # - timing windows and inclusions
    for order in itertools.permutations(cities):
        # Quick prune: adjacency
        if not is_path_with_direct_flights(order, graph):
            continue

        # Compute inclusive day ranges with overlap-on-transition rule
        ranges = compute_day_ranges(order, durations, start_day=1)

        # Validate trip spans exactly Day 1..20 in calendar time
        last_city = order[-1]
        if ranges[last_city][1] != total_days:
            continue  # must end on Day 20

        # Check window constraints
        ok = True
        for city, rule in windows.items():
            rng = ranges[city]
            if "must_include_days" in rule:
                if not range_includes_days(rng, rule["must_include_days"]):
                    ok = False
                    break
            if "must_intersect" in rule:
                if not range_intersects(rng, rule["must_intersect"]):
                    ok = False
                    break

        if not ok:
            continue

        # Found a valid itinerary; choose the first (can be considered "optimal" under our search order)
        best_order = order
        best_ranges = ranges
        break

    if not best_order:
        return {"error": "No feasible itinerary found under given constraints."}

    # Build output
    itinerary = []
    for city in best_order:
        s, e = best_ranges[city]
        itinerary.append({"day_range": f"Day {s}-{e}", "place": city})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = find_itinerary()
    print(json.dumps(result, ensure_ascii=False))