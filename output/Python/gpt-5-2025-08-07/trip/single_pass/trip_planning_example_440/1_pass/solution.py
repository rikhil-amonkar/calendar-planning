import itertools
import json

def build_adjacency(edges):
    adj = {}
    for a, b in edges:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    return adj

def is_hamiltonian_path(path, adj):
    return all(path[i+1] in adj.get(path[i], set()) for i in range(len(path)-1))

def compute_intervals_for_path(path, required_days, total_days):
    # Compute start/end days for each city along the path using the "flight day counts for both" rule
    starts = {}
    ends = {}
    s = 1
    for city in path:
        e = s + required_days[city] - 1
        starts[city] = s
        ends[city] = e
        s = e  # next city's start equals current end (flight day overlaps)
    # Validate total days consistency
    if ends[path[-1]] != total_days:
        return None
    return starts, ends

def windows_satisfied(starts, ends, windows):
    for city, intervals in windows.items():
        for a, b in intervals:
            if not (starts[city] <= a and ends[city] >= b):
                return False
    return True

def validate_counts_with_presence(starts, ends, required_days, total_days, path):
    # Optional rigorous check: build per-day presence and ensure counts match
    # Presence model: a city is present on all days from start to end inclusive
    counts = {c: 0 for c in required_days}
    for day in range(1, total_days + 1):
        for city in required_days:
            if starts[city] <= day <= ends[city]:
                counts[city] += 1
    return counts == required_days

def main():
    # INPUT VARIABLES
    total_days = 12
    cities = ["Geneva", "Split", "Vilnius", "Helsinki", "Reykjavik"]
    required_days = {
        "Split": 2,
        "Helsinki": 2,
        "Reykjavik": 3,
        "Vilnius": 3,
        "Geneva": 6,
    }
    # Windows: inclusive day ranges that must be fully contained in the city's presence
    windows = {
        "Reykjavik": [(10, 12)],  # attending the wedding
        "Vilnius": [(7, 9)],      # visiting relatives
    }
    # Direct flight pairs (undirected)
    direct_flights = [
        ("Split", "Helsinki"),
        ("Geneva", "Split"),
        ("Geneva", "Helsinki"),
        ("Helsinki", "Reykjavik"),
        ("Vilnius", "Helsinki"),
        ("Split", "Vilnius"),
    ]

    # Build adjacency
    adj = build_adjacency(direct_flights)

    # Search all Hamiltonian paths that satisfy adjacency and constraints
    valid_plans = []
    for path in itertools.permutations(cities):
        if not is_hamiltonian_path(path, adj):
            continue
        # Compute city presence intervals based on required days
        result = compute_intervals_for_path(path, required_days, total_days)
        if result is None:
            continue
        starts, ends = result
        # Check windows (e.g., wedding/relatives)
        if not windows_satisfied(starts, ends, windows):
            continue
        # Confirm counts align exactly
        if not validate_counts_with_presence(starts, ends, required_days, total_days, path):
            continue
        # If all constraints satisfied, record plan
        valid_plans.append((path, starts, ends))

    if not valid_plans:
        # If no valid plan found, output an empty itinerary to remain valid JSON
        print(json.dumps({"itinerary": []}))
        return

    # Choose an "optimal" plan deterministically: lexicographically smallest path tuple
    valid_plans.sort(key=lambda x: x[0])
    best_path, starts, ends = valid_plans[0]

    itinerary = []
    for city in best_path:
        itinerary.append({
            "day_range": f"Day {starts[city]}-{ends[city]}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()