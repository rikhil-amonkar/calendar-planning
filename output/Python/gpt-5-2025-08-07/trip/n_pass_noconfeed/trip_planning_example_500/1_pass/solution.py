import json
import itertools

def build_adjacency(edges):
    adj = {}
    for a, b, bidir in edges:
        adj.setdefault(a, set()).add(b)
        if bidir:
            adj.setdefault(b, set()).add(a)
        else:
            adj.setdefault(b, set())
    return adj

def compute_itinerary(cities, durations, total_days, forced_ranges, direct_flights):
    adj = build_adjacency(direct_flights)

    # Validate forced ranges match durations for forced cities
    for city, (fs, fe) in forced_ranges.items():
        if durations[city] != (fe - fs + 1):
            raise ValueError(f"Forced range for {city} does not match its duration")

    # Quick feasibility check: sum of durations must equal total_days + (num_cities - 1)
    if sum(durations.values()) != total_days + (len(cities) - 1):
        raise ValueError("Durations sum must equal total_days + (number of flights), where flights = number_of_cities - 1")

    # Try all permutations to find a valid sequence that satisfies:
    # - direct flights between consecutive cities
    # - forced day ranges
    # - total days end at 'total_days'
    for perm in itertools.permutations(cities):
        # Compute day ranges using overlap rule (flight on end day)
        segments = []
        current_start = 1
        valid_edges = True

        for i, city in enumerate(perm):
            start = current_start
            end = start + durations[city] - 1
            segments.append((city, start, end))
            if i < len(perm) - 1:
                next_city = perm[i + 1]
                if next_city not in adj.get(city, set()):
                    valid_edges = False
                    break
            current_start = end

        if not valid_edges:
            continue

        # Check calendar end day
        if segments[-1][2] != total_days:
            continue

        # Check forced ranges
        forced_ok = True
        segment_map = {c: (s, e) for c, s, e in segments}
        for city, (fs, fe) in forced_ranges.items():
            if city not in segment_map or segment_map[city] != (fs, fe):
                forced_ok = False
                break
        if not forced_ok:
            continue

        # All checks passed; build JSON-friendly itinerary
        itinerary = []
        for city, start, end in segments:
            itinerary.append({"day_range": f"Day {start}-{end}", "place": city})

        return {"itinerary": itinerary}

    # If no permutation found, return an error message in JSON format
    return {
        "error": "No valid itinerary could be found with the given constraints."
    }

if __name__ == "__main__":
    # Input variables (trip constraints)
    total_days = 20
    durations = {
        "Hamburg": 7,
        "Munich": 6,
        "Manchester": 2,
        "Lyon": 2,
        "Split": 7
    }
    cities = list(durations.keys())

    # Forced day ranges: inclusive (must be present in city)
    forced_ranges = {
        "Lyon": (13, 14),        # Annual show in Lyon on days 13-14
        "Manchester": (19, 20)   # Visit relatives in Manchester on days 19-20
    }

    # Direct flights: (cityA, cityB, bidirectional)
    direct_flights = [
        ("Split", "Munich", True),
        ("Munich", "Manchester", True),
        ("Hamburg", "Manchester", True),
        ("Hamburg", "Munich", True),
        ("Split", "Lyon", True),
        ("Lyon", "Munich", True),
        ("Hamburg", "Split", True),
        ("Manchester", "Split", False)  # one-way from Manchester to Split
    ]

    result = compute_itinerary(cities, durations, total_days, forced_ranges, direct_flights)
    print(json.dumps(result, ensure_ascii=False))