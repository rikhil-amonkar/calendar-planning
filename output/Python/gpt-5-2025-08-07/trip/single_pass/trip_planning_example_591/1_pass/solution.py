import json
import itertools

def build_adjacency(edges):
    adj = {}
    for a, b in edges:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    return adj

def compute_ranges(order, durations):
    ranges = {}
    prev_end = None
    for i, city in enumerate(order):
        if i == 0:
            start = 1
        else:
            start = prev_end  # flight day overlaps both cities
        end = start + durations[city] - 1
        ranges[city] = (start, end)
        prev_end = end
    total_span_days = prev_end
    return ranges, total_span_days

def intersects(a, b):
    return max(a[0], b[0]) <= min(a[1], b[1])

def find_itinerary(cities, durations, edges, total_days, time_windows, must_start_city=None):
    adj = build_adjacency(edges)
    all_cities = list(cities)

    # Generate candidate orders (Hamiltonian paths) and validate constraints
    if must_start_city:
        start = must_start_city
        others = [c for c in all_cities if c != start]
        start_orders = ([start] + list(p) for p in itertools.permutations(others))
    else:
        start_orders = (list(p) for p in itertools.permutations(all_cities))

    for order in start_orders:
        # Direct-flight check
        if any(order[i+1] not in adj.get(order[i], set()) for i in range(len(order)-1)):
            continue

        # Compute day ranges with 1-day overlap on flight days
        ranges, span = compute_ranges(order, durations)

        # Total span must match overall trip length
        if span != total_days:
            continue

        # Check city durations exactly (implicitly satisfied by how we compute ranges)

        # Time window constraints: must be in city at least one day within specified window
        windows_ok = True
        for city, window in time_windows.items():
            if not intersects(ranges[city], window):
                windows_ok = False
                break
        if not windows_ok:
            continue

        # Build itinerary output preserving the visiting order
        itinerary = []
        for city in order:
            start, end = ranges[city]
            itinerary.append({
                "day_range": f"Day {start}-{end}",
                "place": city
            })
        return {"itinerary": itinerary}

    # If no itinerary found, return empty itinerary with a note
    return {"itinerary": []}

def main():
    # Input variables (constraints)
    cities = ["Geneva", "Munich", "Valencia", "Stuttgart", "Bucharest"]
    durations = {
        "Stuttgart": 2,
        "Bucharest": 2,
        "Geneva": 4,
        "Valencia": 6,
        "Munich": 7
    }
    total_days = 17
    # Direct flights (undirected)
    edges = [
        ("Geneva", "Munich"),
        ("Munich", "Valencia"),
        ("Bucharest", "Valencia"),
        ("Munich", "Bucharest"),
        ("Valencia", "Stuttgart"),
        ("Geneva", "Valencia")
    ]
    # Time windows (inclusive): must be in these cities during these day ranges
    time_windows = {
        "Geneva": (1, 4),   # visit relatives in Geneva between day 1 and day 4
        "Munich": (4, 10)   # meet friends in Munich between day 4 and day 10
    }
    # To satisfy the Geneva window starting at day 1, anchor start in Geneva
    result = find_itinerary(
        cities=cities,
        durations=durations,
        edges=edges,
        total_days=total_days,
        time_windows=time_windows,
        must_start_city="Geneva"
    )

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()