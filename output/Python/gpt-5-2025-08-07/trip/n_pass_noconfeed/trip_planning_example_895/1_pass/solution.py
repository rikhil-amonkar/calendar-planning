import itertools
import json

def build_adjacency(undirected_pairs, directed_pairs):
    adj = {}
    def add(a, b):
        adj.setdefault(a, set()).add(b)

    # Undirected edges
    for a, b in undirected_pairs:
        add(a, b)
        add(b, a)
    # Directed edges
    for a, b in directed_pairs:
        add(a, b)
    return adj

def compute_flight_days(order, durations):
    # t[i] = flight day from order[i] to order[i+1]
    t = []
    acc = durations[order[0]]
    t.append(acc)
    for i in range(1, len(order)-1):
        acc += durations[order[i]] - 1
        t.append(acc)
    return t

def compute_intervals(order, durations, total_days):
    t = compute_flight_days(order, durations)
    intervals = {}
    for idx, city in enumerate(order):
        if idx == 0:
            start = 1
        else:
            start = t[idx-1]
        if idx < len(order)-1:
            end = t[idx]
        else:
            end = total_days
        intervals[city] = (start, end)
    return intervals

def itinerary_search():
    # Input variables derived from the prompt
    total_days = 17
    cities = ["Venice", "London", "Lisbon", "Brussels", "Reykjavik", "Santorini", "Madrid"]
    durations = {
        "Venice": 3,
        "London": 3,
        "Lisbon": 4,
        "Brussels": 2,
        "Reykjavik": 3,
        "Santorini": 3,
        "Madrid": 5,
    }
    # Direct flights
    undirected_pairs = [
        ("Venice", "Madrid"),
        ("Lisbon", "Reykjavik"),
        ("Brussels", "Venice"),
        ("Venice", "Santorini"),
        ("Lisbon", "Venice"),
        ("Brussels", "London"),
        ("Madrid", "London"),
        ("Santorini", "London"),
        ("London", "Reykjavik"),
        ("Brussels", "Lisbon"),
        ("Lisbon", "London"),
        ("Lisbon", "Madrid"),
        ("Madrid", "Santorini"),
        ("Brussels", "Reykjavik"),
        ("Brussels", "Madrid"),
        ("Venice", "London"),
    ]
    directed_pairs = [
        ("Reykjavik", "Madrid")
    ]
    adjacency = build_adjacency(undirected_pairs, directed_pairs)

    # Windows: inclusive day ranges that must be fully covered while in the specified city
    windows = [
        {"city": "Brussels", "start": 1, "end": 2},   # conference
        {"city": "Venice", "start": 5, "end": 7},     # visit relatives
        {"city": "Madrid", "start": 7, "end": 11},    # wedding
    ]

    # Validate global feasibility based on sums
    sum_durations = sum(durations.values())
    required_flights = sum_durations - total_days
    if required_flights != len(cities) - 1:
        raise ValueError("Infeasible: durations and total days imply flights != city transitions.")

    # Search for a valid path/order of cities
    start_city = "Brussels"
    remaining = [c for c in cities if c != start_city]

    def is_direct(a, b):
        return b in adjacency.get(a, set())

    for perm in itertools.permutations(remaining):
        order = [start_city] + list(perm)

        # Check direct flights along the path
        ok_edges = True
        for i in range(len(order) - 1):
            if not is_direct(order[i], order[i+1]):
                ok_edges = False
                break
        if not ok_edges:
            continue

        # Compute intervals for each city
        intervals = compute_intervals(order, durations, total_days)

        # Check windows
        windows_ok = True
        for w in windows:
            city = w["city"]
            ws, we = w["start"], w["end"]
            cs, ce = intervals[city]
            if not (cs <= ws and ce >= we):
                windows_ok = False
                break
        if not windows_ok:
            continue

        # Found a valid itinerary
        # Build output ranges in the requested format
        itinerary = []
        for city in order:
            s, e = intervals[city]
            itinerary.append({"day_range": f"Day {s}-{e}", "place": city})

        return {"itinerary": itinerary}

    # If search fails
    raise RuntimeError("No valid itinerary found with the given constraints.")

if __name__ == "__main__":
    result = itinerary_search()
    print(json.dumps(result))