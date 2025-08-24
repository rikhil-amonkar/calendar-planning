import itertools
import json

def build_adjacency(cities):
    # Initialize adjacency map
    adj = {c: set() for c in cities}
    # Bidirectional routes (A and B)
    bidir_pairs = [
        ("Bucharest", "Vienna"),
        ("Reykjavik", "Vienna"),
        ("Manchester", "Vienna"),
        ("Manchester", "Riga"),
        ("Riga", "Vienna"),
        ("Istanbul", "Vienna"),
        ("Vienna", "Florence"),
        ("Stuttgart", "Vienna"),
        ("Riga", "Bucharest"),
        ("Istanbul", "Riga"),
        ("Stuttgart", "Istanbul"),
        ("Istanbul", "Bucharest"),
        ("Manchester", "Istanbul"),
        ("Manchester", "Bucharest"),
        ("Stuttgart", "Manchester"),
    ]
    for a, b in bidir_pairs:
        adj[a].add(b)
        adj[b].add(a)
    # Directed route
    adj["Reykjavik"].add("Stuttgart")  # from Reykjavik to Stuttgart
    return adj

def compute_day_ranges(order, durations):
    # Calculate start and end days for each city given the order
    starts = {}
    ends = {}
    s = 1
    for i, city in enumerate(order):
        starts[city] = s
        ends[city] = s + durations[city] - 1
        s = ends[city]  # next city starts (overlapping travel day)
    return starts, ends

def is_valid_order(order, durations, total_days, adj, must_be_at):
    # Check route connectivity (direct flights)
    for i in range(len(order) - 1):
        a, b = order[i], order[i+1]
        if b not in adj[a]:
            return False, None

    # Compute day ranges
    starts, ends = compute_day_ranges(order, durations)

    # Check trip total days matches
    last_end = ends[order[-1]]
    if last_end != total_days:
        return False, None

    # Enforce special date constraints (exact cover because durations are fixed)
    for city, spec in must_be_at.items():
        required_start, required_duration = spec["start"], spec["duration"]
        if durations[city] != required_duration or starts[city] != required_start:
            return False, None

    return True, (starts, ends)

def build_itinerary(order, starts, ends):
    itinerary = []
    for city in order:
        itinerary.append({
            "day_range": f"Day {starts[city]}-{ends[city]}",
            "place": city
        })
    return itinerary

def main():
    # Input variables (constraints)
    total_days = 23
    city_durations = {
        "Riga": 4,
        "Manchester": 5,
        "Bucharest": 4,
        "Florence": 4,
        "Vienna": 2,
        "Istanbul": 2,
        "Reykjavik": 4,
        "Stuttgart": 5
    }
    # Special fixed-date events (must be in these cities on these day ranges)
    must_be_at = {
        "Istanbul": {"start": 12, "duration": 2},   # Days 12-13
        "Bucharest": {"start": 16, "duration": 4}   # Days 16-19
    }

    cities = list(city_durations.keys())
    adj = build_adjacency(cities)

    # Search for a valid permutation that satisfies all constraints
    found_solution = None
    for order in itertools.permutations(cities):
        valid, se = is_valid_order(order, city_durations, total_days, adj, must_be_at)
        if valid:
            starts, ends = se
            itinerary = build_itinerary(order, starts, ends)
            found_solution = {"itinerary": itinerary}
            break

    if not found_solution:
        # Should not happen for given constraints; but produce a clear JSON in case
        print(json.dumps({"error": "No valid itinerary found with given constraints."}, ensure_ascii=False))
    else:
        print(json.dumps(found_solution, ensure_ascii=False))

if __name__ == "__main__":
    main()