import itertools
import json
from collections import defaultdict

def build_adjacency(edges):
    adj = defaultdict(set)
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    return adj

def compute_day_ranges(order, durations, start_day=1):
    # Returns dict: city -> (start, end) with overlap on transition days
    day_ranges = {}
    current_start = start_day
    for city in order:
        dur = durations[city]
        end_day = current_start + dur - 1
        day_ranges[city] = (current_start, end_day)
        current_start = end_day  # next segment starts on the same end day (flight day overlap)
    return day_ranges

def is_range_covering(day_range, window):
    # True if [start,end] fully covers [w_start, w_end]
    start, end = day_range
    w_start, w_end = window
    return start <= w_start and end >= w_end

def find_itinerary(cities, durations, total_days, direct_edges, required_windows_full):
    adjacency = build_adjacency(direct_edges)

    # Basic feasibility check: sum(durations) - (n_cities - 1) must equal total_days
    total_required = sum(durations[c] for c in cities)
    if total_required - (len(cities) - 1) != total_days:
        return None

    # Search permutations
    for order in itertools.permutations(cities):
        # Check direct flights between consecutive cities
        valid_route = True
        for i in range(len(order) - 1):
            if order[i+1] not in adjacency[order[i]]:
                valid_route = False
                break
        if not valid_route:
            continue

        day_ranges = compute_day_ranges(order, durations, start_day=1)

        # Last day's end must equal total_days
        last_city = order[-1]
        if day_ranges[last_city][1] != total_days:
            continue

        # Enforce windows that must be fully covered
        windows_ok = True
        for city, window in required_windows_full.items():
            if not is_range_covering(day_ranges[city], window):
                windows_ok = False
                break
        if not windows_ok:
            continue

        # Found feasible itinerary
        itinerary = []
        for city in order:
            s, e = day_ranges[city]
            itinerary.append({"day_range": f"Day {s}-{e}", "place": city})
        return {"itinerary": itinerary}

    return None

def main():
    # Input variables (trip constraints)
    total_days = 16
    cities = ["Porto", "Prague", "Reykjavik", "Santorini", "Amsterdam", "Munich"]
    durations = {
        "Porto": 5,
        "Prague": 4,
        "Reykjavik": 4,
        "Santorini": 2,
        "Amsterdam": 2,
        "Munich": 4,
    }
    direct_edges = [
        ("Porto", "Amsterdam"),
        ("Munich", "Amsterdam"),
        ("Reykjavik", "Amsterdam"),
        ("Munich", "Porto"),
        ("Prague", "Reykjavik"),
        ("Reykjavik", "Munich"),
        ("Amsterdam", "Santorini"),
        ("Prague", "Amsterdam"),
        ("Prague", "Munich"),
    ]
    # Event windows that must be fully covered by presence in that city
    # Interpreted strictly to ensure attendance throughout these windows
    required_windows_full = {
        "Reykjavik": (4, 7),   # wedding window
        "Munich": (7, 10),     # friend meeting window
        "Amsterdam": (14, 15), # conference window
    }

    result = find_itinerary(cities, durations, total_days, direct_edges, required_windows_full)
    if result is None:
        # Fallback: output an empty itinerary if no plan found (should not happen with given constraints)
        print(json.dumps({"itinerary": []}, ensure_ascii=False))
    else:
        print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()