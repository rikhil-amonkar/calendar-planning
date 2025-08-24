import json
import itertools
from collections import defaultdict

def build_adjacency(undirected_pairs, directed_pairs):
    adj = defaultdict(set)
    for a, b in undirected_pairs:
        adj[a].add(b)
        adj[b].add(a)
    for a, b in directed_pairs:
        adj[a].add(b)
    return adj

def compute_day_ranges(order, durations, total_days):
    # Overlapping schedule: each transition day counts for both cities
    day_ranges = {}
    start = 1
    for i, city in enumerate(order):
        end = start + durations[city] - 1
        day_ranges[city] = (start, end)
        start = end  # next city starts on the same day (flight day overlap)
    # Validate total days end
    if day_ranges[order[-1]][1] != total_days:
        return None
    return day_ranges

def satisfies_presence_constraints(day_ranges, presence_constraints):
    for city, (req_start, req_end) in presence_constraints.items():
        if city not in day_ranges:
            return False
        start, end = day_ranges[city]
        # City must include all days in the required inclusive interval
        if not (start <= req_start and end >= req_end):
            return False
    return True

def path_has_direct_flights(order, adjacency):
    for a, b in zip(order, order[1:]):
        if b not in adjacency[a]:
            return False
    return True

def main():
    # Input variables (constraints)
    total_days = 14
    cities = ["Helsinki", "Warsaw", "Madrid", "Split", "Reykjavik", "Budapest"]
    durations = {
        "Helsinki": 2,
        "Warsaw": 3,
        "Madrid": 4,
        "Split": 4,
        "Reykjavik": 2,
        "Budapest": 4,
    }
    # Presence constraints: city must include the full inclusive day window
    presence_constraints = {
        "Helsinki": (1, 2),   # workshop days 1-2
        "Warsaw": (9, 11),    # relatives days 9-11
        "Reykjavik": (8, 9),  # meet friend days 8-9
    }
    # Direct flights
    undirected_pairs = [
        ("Helsinki", "Reykjavik"),
        ("Budapest", "Warsaw"),
        ("Madrid", "Split"),
        ("Helsinki", "Split"),
        ("Helsinki", "Madrid"),
        ("Helsinki", "Budapest"),
        ("Reykjavik", "Warsaw"),
        ("Helsinki", "Warsaw"),
        ("Madrid", "Budapest"),
        ("Budapest", "Reykjavik"),
        ("Madrid", "Warsaw"),
        ("Warsaw", "Split"),
    ]
    directed_pairs = [
        ("Reykjavik", "Madrid"),  # one-way
    ]
    adjacency = build_adjacency(undirected_pairs, directed_pairs)

    # Verify basic feasibility: sum of durations - (n-1) must equal total_days
    sum_durations = sum(durations[c] for c in cities)
    if sum_durations - (len(cities) - 1) != total_days:
        raise ValueError("Durations and total days are inconsistent with overlap flight rule.")

    # Search for a valid route starting in Helsinki that satisfies all constraints and direct flights
    start_city = "Helsinki"
    remaining = [c for c in cities if c != start_city]

    valid_itinerary = None

    for perm in itertools.permutations(remaining):
        order = [start_city] + list(perm)
        # Must include all cities exactly once (permutation ensures this)
        # Check direct flights connectivity in order
        if not path_has_direct_flights(order, adjacency):
            continue
        # Compute day ranges using overlap rule
        day_ranges = compute_day_ranges(order, durations, total_days)
        if day_ranges is None:
            continue
        # Check presence constraints (specific days in specific cities)
        if not satisfies_presence_constraints(day_ranges, presence_constraints):
            continue
        # Found a valid itinerary
        valid_itinerary = [(city, day_ranges[city]) for city in order]
        break

    if not valid_itinerary:
        # If no valid itinerary found, raise error (should not happen with given data)
        raise RuntimeError("No valid itinerary satisfying all constraints was found.")

    # Build JSON-friendly output
    itinerary_output = []
    for city, (start, end) in valid_itinerary:
        itinerary_output.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary_output}, ensure_ascii=False))

if __name__ == "__main__":
    main()