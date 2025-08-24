import itertools
import json

def build_adjacency(cities, undirected_edges, directed_edges):
    adj = {c: set() for c in cities}
    for a, b in undirected_edges:
        adj[a].add(b)
        adj[b].add(a)
    for a, b in directed_edges:
        adj[a].add(b)
    return adj

def is_valid_path(order, adj):
    # Check direct flight availability between consecutive cities
    for i in range(len(order) - 1):
        if order[i+1] not in adj[order[i]]:
            return False
    return True

def compute_ranges(order, durations, total_days):
    # Sequential allocation with 1-day overlaps: start_i = end_{i-1}
    ranges = {}
    current_start = 1
    for i, city in enumerate(order):
        if i == 0:
            start = current_start
        else:
            start = prev_end  # overlap day counts for both cities (flight day)
        end = start + durations[city] - 1
        ranges[city] = (start, end)
        prev_end = end
    # Sanity: last end must equal total_days
    if prev_end != total_days:
        return None
    return ranges

def intersects(a, b):
    return not (a[1] < b[0] or b[1] < a[0])

def intersection(a, b):
    lo = max(a[0], b[0])
    hi = min(a[1], b[1])
    if lo <= hi:
        return (lo, hi)
    return None

def window_penalty(city_range, window):
    # Penalty = distance of window center to the intersection with city range.
    # If center lies inside intersection, penalty 0. Otherwise distance to nearest bound.
    inter = intersection(city_range, window)
    if inter is None:
        return float('inf')
    center = (window[0] + window[1]) / 2.0
    lo, hi = inter
    if lo <= center <= hi:
        return 0.0
    elif center < lo:
        return lo - center
    else:
        return center - hi

def validate_constraints(ranges, window_constraints):
    # Ensure each city with a window constraint has at least one day overlapping the window
    for city, win in window_constraints.items():
        if not intersects(ranges[city], win):
            return False
    return True

def score_itinerary(order, ranges, window_constraints):
    # Sum penalties for all window-constrained cities; lower is better
    total_pen = 0.0
    for city, win in window_constraints.items():
        total_pen += window_penalty(ranges[city], win)
    # Tie-breaker: lexicographic on order string (stable, deterministic)
    tiebreak = "->".join(order)
    return (total_pen, tiebreak)

def main():
    # Input variables (trip constraints)
    total_days = 17
    cities = ["Brussels", "Rome", "Dubrovnik", "Geneva", "Budapest", "Riga", "Valencia"]
    durations = {
        "Brussels": 5,
        "Rome": 2,
        "Dubrovnik": 3,
        "Geneva": 5,
        "Budapest": 2,
        "Riga": 4,
        "Valencia": 2
    }
    # Windows: inclusive day ranges
    window_constraints = {
        "Brussels": (7, 11),   # Workshop between day 7 and 11
        "Riga": (4, 7),        # Friends in Riga between day 4 and 7
        "Budapest": (16, 17)   # Meet friend in Budapest between day 16 and 17
    }

    undirected_edges = [
        ("Brussels", "Valencia"),
        ("Rome", "Valencia"),
        ("Brussels", "Geneva"),
        ("Rome", "Geneva"),
        ("Dubrovnik", "Geneva"),
        ("Valencia", "Geneva"),
        ("Geneva", "Budapest"),
        ("Riga", "Brussels"),
        ("Rome", "Budapest"),
        ("Rome", "Brussels"),
        ("Brussels", "Budapest"),
        ("Dubrovnik", "Rome"),
    ]
    directed_edges = [
        ("Rome", "Riga")
    ]

    # Build adjacency for direct flights
    adj = build_adjacency(cities, undirected_edges, directed_edges)

    # Validate simple sums: ensure total overlaps match
    required_sum = sum(durations.values())
    required_flights = len(cities) - 1
    if required_sum - required_flights != total_days:
        raise ValueError("Duration totals cannot fit into the total days with 1-day overlaps between cities.")

    best = None  # (score_tuple, order, ranges)
    for order in itertools.permutations(cities):
        # Quick directional pre-check: Rome must appear before Riga if Rome->Riga is used in adjacency and there is no Riga->Rome
        if "Rome" in order and "Riga" in order:
            if order.index("Rome") > order.index("Riga"):
                # The only way Riga could connect to Rome would be Riga->Rome, which is not allowed
                # However, Riga could connect to Brussels instead without Rome adjacency, so we cannot prune solely on this.
                # We'll leave this pre-check commented out and rely on path validation.
                pass

        if not is_valid_path(order, adj):
            continue

        ranges = compute_ranges(order, durations, total_days)
        if ranges is None:
            continue

        if not validate_constraints(ranges, window_constraints):
            continue

        score = score_itinerary(order, ranges, window_constraints)
        if best is None or score < best[0]:
            best = (score, order, ranges)

    if best is None:
        raise RuntimeError("No valid itinerary found that satisfies all constraints with direct flights only.")

    _, best_order, best_ranges = best

    # Build output itinerary in order with day ranges
    itinerary = []
    for city in best_order:
        start, end = best_ranges[city]
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()