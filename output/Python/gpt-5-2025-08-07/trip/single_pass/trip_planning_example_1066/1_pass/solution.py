import json
import itertools

def build_adjacency(direct_flights):
    adj = {}
    for a, b in direct_flights:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    return adj

def compute_day_ranges(order, durations):
    itinerary = []
    ranges = {}
    s = 1
    for city in order:
        e = s + durations[city] - 1
        itinerary.append({"day_range": f"Day {s}-{e}", "place": city})
        ranges[city] = (s, e)
        s = e  # overlap by 1 day with next city (flight day counts for both)
    return itinerary, ranges

def is_feasible(order, durations, adj, total_days, stuttgart_window=(1,4), madrid_conf_days=(20,21)):
    # Check adjacency (direct flights only)
    for i in range(len(order) - 1):
        if order[i+1] not in adj.get(order[i], set()):
            return False

    # Compute ranges
    itinerary, ranges = compute_day_ranges(order, durations)

    # The last day's end should match total_days
    last_end = ranges[order[-1]][1]
    if last_end != total_days:
        return False

    # Stuttgart meeting window constraint
    s_st, e_st = ranges["Stuttgart"]
    if not (s_st <= stuttgart_window[1] and e_st >= stuttgart_window[0]):
        return False

    # Madrid conference on specific days
    s_mad, e_mad = ranges["Madrid"]
    if not (s_mad <= madrid_conf_days[0] and e_mad >= madrid_conf_days[1]):
        return False

    # Ensure Madrid duration exactly as specified
    if (e_mad - s_mad + 1) != durations["Madrid"]:
        return False

    return itinerary

def find_itinerary():
    # Input variables (constraints)
    total_days = 21
    durations = {
        "Brussels": 4,
        "Bucharest": 3,
        "Stuttgart": 4,
        "Mykonos": 2,
        "Madrid": 2,       # Must be on Day 20-21
        "Helsinki": 5,
        "Split": 3,
        "London": 5
    }

    direct_flights = [
        ("Helsinki", "London"),
        ("Split", "Madrid"),
        ("Helsinki", "Madrid"),
        ("London", "Madrid"),
        ("Brussels", "London"),
        ("Bucharest", "London"),
        ("Brussels", "Bucharest"),
        ("Bucharest", "Madrid"),
        ("Split", "Helsinki"),
        ("Mykonos", "Madrid"),
        ("Stuttgart", "London"),
        ("Helsinki", "Brussels"),
        ("Brussels", "Madrid"),
        ("Split", "London"),
        ("Stuttgart", "Split"),
        ("London", "Mykonos"),
    ]

    # Validate overall feasibility: sum(durations) must equal unique_days + overlaps
    # overlaps = number of transitions = number_of_cities - 1
    cities = list(durations.keys())
    n = len(cities)
    if sum(durations.values()) != total_days + (n - 1):
        return []

    adj = build_adjacency(direct_flights)

    # Madrid must include Day 20-21 -> Madrid must be last given durations (2 days)
    non_madrid = [c for c in cities if c != "Madrid"]

    # Heuristic ordering to find a feasible solution quickly (still algorithmic search)
    # This ordering mirrors connectivity and constraints (Stuttgart early, Madrid last).
    seed_order = ["Stuttgart", "Split", "Helsinki", "Brussels", "Bucharest", "London", "Mykonos"]
    # Ensure we permute over the exact set
    if set(seed_order) != set(non_madrid):
        non_madrid = sorted(non_madrid)  # fallback

    for perm in itertools.permutations(non_madrid):
        order = list(perm) + ["Madrid"]
        itinerary = is_feasible(order, durations, adj, total_days)
        if itinerary:
            return itinerary

    # If not found, return empty itinerary
    return []

def main():
    itinerary = find_itinerary()
    result = {"itinerary": itinerary}
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()