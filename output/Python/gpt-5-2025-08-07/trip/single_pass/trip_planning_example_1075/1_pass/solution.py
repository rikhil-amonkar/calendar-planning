import itertools
import json

def build_adjacency(edges, cities):
    adj = {c: set() for c in cities}
    for a, b in edges:
        if a in adj and b in adj:
            adj[a].add(b)
            adj[b].add(a)  # undirected
    return adj

def compute_day_ranges(order, durations):
    ranges = []
    for i, city in enumerate(order):
        if i == 0:
            start = 1
        else:
            start = ranges[-1][2]  # overlap flight day counts in both cities
        end = start + durations[city] - 1
        ranges.append((city, start, end))
    return ranges

def is_valid(order, durations, adj, total_days, must_in_city_ranges):
    # Check direct flights between consecutive cities
    for i in range(len(order) - 1):
        if order[i+1] not in adj[order[i]]:
            return False

    ranges = compute_day_ranges(order, durations)
    city_to_range = {c: (s, e) for c, s, e in ranges}

    # Check total calendar days
    if ranges[-1][2] != total_days:
        return False

    # Check specific city-day window constraints
    for city, (req_start, req_end) in must_in_city_ranges.items():
        s, e = city_to_range[city]
        # Must exactly match since durations are fixed and must include the window
        if not (s == req_start and e == req_end):
            return False

    return True

def main():
    # Input variables (constraints)
    total_days = 25
    city_durations = {
        "Vienna": 4,
        "Lyon": 3,
        "Edinburgh": 4,
        "Reykjavik": 5,
        "Stuttgart": 5,
        "Manchester": 2,
        "Split": 5,
        "Prague": 4,
    }

    # Direct flight connections (treated as undirected)
    edges = [
        ("Reykjavik", "Stuttgart"),
        ("Stuttgart", "Split"),
        ("Stuttgart", "Vienna"),
        ("Prague", "Manchester"),
        ("Edinburgh", "Prague"),
        ("Manchester", "Split"),
        ("Prague", "Vienna"),
        ("Vienna", "Manchester"),
        ("Prague", "Split"),
        ("Vienna", "Lyon"),
        ("Stuttgart", "Edinburgh"),
        ("Split", "Lyon"),
        ("Stuttgart", "Manchester"),
        ("Prague", "Lyon"),
        ("Reykjavik", "Vienna"),
        ("Prague", "Reykjavik"),
        ("Vienna", "Split"),
    ]

    cities = sorted(city_durations.keys())

    # Must be in Edinburgh on days 5-8 (inclusive), and in Split on days 19-23
    must_in_city_ranges = {
        "Edinburgh": (5, 8),
        "Split": (19, 23),
    }

    adj = build_adjacency(edges, cities)

    found_order = None
    for order in itertools.permutations(cities):
        if is_valid(order, city_durations, adj, total_days, must_in_city_ranges):
            found_order = order
            break

    if not found_order:
        print(json.dumps({"error": "No valid itinerary found given the constraints."}))
        return

    # Build itinerary output
    ranges = compute_day_ranges(found_order, city_durations)
    itinerary = []
    for city, start, end in ranges:
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()