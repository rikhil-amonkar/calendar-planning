import json
from collections import defaultdict
from itertools import permutations

def main():
    # Input variables (constraints)
    total_days = 20
    cities = ["Berlin", "Nice", "Athens", "Stockholm", "Barcelona", "Vilnius", "Lyon"]
    required_stays = {
        "Berlin": 3,
        "Nice": 5,
        "Athens": 5,
        "Stockholm": 5,
        "Barcelona": 2,
        "Vilnius": 4,
        "Lyon": 2,
    }
    # Specific day-presence constraints (must be in these cities on these days)
    must_be_days = {
        "Berlin": {1, 3},
        "Barcelona": {3, 4},
        "Lyon": {4, 5},
    }
    # Direct flights (undirected)
    edges = [
        ("Lyon", "Nice"),
        ("Stockholm", "Athens"),
        ("Nice", "Athens"),
        ("Berlin", "Athens"),
        ("Berlin", "Nice"),
        ("Berlin", "Barcelona"),
        ("Berlin", "Vilnius"),
        ("Barcelona", "Nice"),
        ("Athens", "Vilnius"),
        ("Berlin", "Stockholm"),
        ("Nice", "Stockholm"),
        ("Barcelona", "Athens"),
        ("Barcelona", "Stockholm"),
        ("Barcelona", "Lyon"),
    ]

    # Build adjacency map
    adj = defaultdict(set)
    edge_set = set()
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
        edge_set.add(frozenset([a, b]))

    def direct(a, b):
        return frozenset([a, b]) in edge_set

    # Helper to expand inclusive day range into set
    def day_set(s, e):
        return set(range(s, e + 1))

    # Minimum number of flight days needed to satisfy all stay totals with total trip length
    min_flights_needed = sum(required_stays.values()) - total_days
    if min_flights_needed < 0:
        raise RuntimeError("Infeasible: total required stays less than total days.")
    # We'll ensure our plan uses exactly this number of flights (optimal/minimal).

    segments = []  # list of dicts {city, start, end}

    # Phase 1: Fix Berlin, Barcelona, Lyon according to hard constraints and compute necessary flights.
    # Berlin must include day 1 and day 3, and total Berlin stay is 3 days -> segment must be Day 1-3
    berlin_start = min(must_be_days["Berlin"])
    berlin_end = max(must_be_days["Berlin"])
    assert berlin_end - berlin_start + 1 == required_stays["Berlin"] == 3
    segments.append({"city": "Berlin", "start": berlin_start, "end": berlin_end})

    # Barcelona must include day 3-4; total Barcelona stay is 2 days -> segment Day 3-4
    # Need a direct flight Berlin->Barcelona on day 3
    assert direct("Berlin", "Barcelona"), "No direct Berlin-Barcelona flight."
    segments.append({"city": "Barcelona", "start": 3, "end": 4})

    # Lyon must include day 4-5; Need direct flight Barcelona->Lyon on day 4
    assert direct("Barcelona", "Lyon"), "No direct Barcelona-Lyon flight."
    segments.append({"city": "Lyon", "start": 4, "end": 5})

    # To not exceed Lyon's 2-day requirement, we must depart Lyon on day 5 to the next city
    # Determine remaining cities
    used_cities = {"Berlin", "Barcelona", "Lyon"}
    remaining_cities = [c for c in cities if c not in used_cities]

    # Pick a neighbor of Lyon among the remaining cities to fly to on day 5
    lyon_neighbors = adj["Lyon"].intersection(remaining_cities)
    if not lyon_neighbors:
        raise RuntimeError("No viable city to depart to from Lyon on day 5.")

    # We need to find a Hamiltonian path through the remaining cities starting at a chosen neighbor,
    # such that each consecutive pair has a direct flight.
    def find_path(start, targets_set, adjacency):
        # DFS to find path that visits all nodes in targets_set exactly once, starting at 'start'
        def dfs(curr, remaining, path):
            if not remaining:
                return path
            for nxt in adjacency[curr]:
                if nxt in remaining:
                    res = dfs(nxt, remaining - {nxt}, path + [nxt])
                    if res:
                        return res
            return None
        return dfs(start, set(targets_set) - {start}, [start])

    start_city = None
    path = None
    for candidate in sorted(lyon_neighbors):
        p = find_path(candidate, remaining_cities, adj)
        if p and len(p) == len(remaining_cities):
            start_city = candidate
            path = p
            break

    if not path:
        raise RuntimeError("Failed to find a viable path through remaining cities from Lyon.")

    # Phase 2: Allocate days for the remaining chain with minimal flights and exact stay counts.
    # We already used flights on days 3 and 4; we will depart Lyon on day 5 to start_city.
    # Start counting the chain at day 5 (flight day), which contributes to both Lyon and start_city.
    chain_start_day = 5

    # Compute segments for each city in the path using the rule:
    # For each city except the last: end = start + required_days[city] - 1, flight occurs on 'end' to next city,
    # Next city's start = end, Last city's end must be total_days.
    # This ensures the total overlaps (flights) equals number of transitions.
    chain_segments = []
    s = chain_start_day
    for i, city in enumerate(path):
        req = required_stays[city]
        e = s + req - 1
        if i < len(path) - 1:
            # Ensure direct flight to next city
            nxt = path[i + 1]
            if not direct(city, nxt):
                raise RuntimeError(f"No direct flight from {city} to {nxt} as required by path.")
            # Schedule segment and move start to the same end day (flight day)
            chain_segments.append({"city": city, "start": s, "end": e})
            s = e  # flight day counts for next city too
        else:
            # Last city must end exactly on total_days
            if e != total_days:
                raise RuntimeError(f"Chain allocation did not end on day {total_days}; got day {e}.")
            chain_segments.append({"city": city, "start": s, "end": e})

    segments.extend(chain_segments)

    # Validation: ensure required stays and presence constraints are met, and flight count is minimal
    # Build day sets per city
    city_days = defaultdict(set)
    for seg in segments:
        city_days[seg["city"]].update(range(seg["start"], seg["end"] + 1))

    # Check exact required stays
    for c, req in required_stays.items():
        if len(city_days[c]) != req:
            raise RuntimeError(f"City {c} has {len(city_days[c])} days, required {req}.")

    # Check specific day presence constraints
    for c, days in must_be_days.items():
        if not days.issubset(city_days[c]):
            raise RuntimeError(f"City {c} is not present on required days {sorted(days)}.")

    # Count flights implied by segments (each transition between consecutive segments is a flight on the day
    # equal to the end of the earlier segment if the next segment starts on the same day).
    # We'll reconstruct the chronological order and count unique transitions by day.
    segments_sorted = sorted(segments, key=lambda x: (x["start"], x["end"]))
    flights = []
    # We know our intended flights (based on construction):
    # Day 3: Berlin -> Barcelona
    flights.append((3, "Berlin", "Barcelona"))
    # Day 4: Barcelona -> Lyon
    flights.append((4, "Barcelona", "Lyon"))
    # Day 5: Lyon -> start_city
    flights.append((5, "Lyon", path[0]))
    # Chain flights:
    for i in range(len(path) - 1):
        from_city = path[i]
        to_city = path[i + 1]
        # Find the segment end for from_city within chain_segments
        from_seg = next(seg for seg in chain_segments if seg["city"] == from_city)
        flight_day = from_seg["end"]
        flights.append((flight_day, from_city, to_city))

    # Validate flight count and directness
    if len(flights) != min_flights_needed:
        raise RuntimeError(f"Flight count {len(flights)} does not match minimal required {min_flights_needed}.")
    for d, a, b in flights:
        if not direct(a, b):
            raise RuntimeError(f"Flight on day {d} from {a} to {b} is not direct.")

        # Ensure we are actually in 'a' and 'b' on the flight day according to segments
        if d not in city_days[a] or d not in city_days[b]:
            raise RuntimeError(f"On day {d}, not present in both {a} and {b} for the flight.")

    # Output itinerary as JSON
    itinerary = []
    # Sort segments chronologically by start (ties broken by city name for determinism)
    for seg in sorted(segments, key=lambda x: (x["start"], x["end"], x["city"])):
        itinerary.append({
            "day_range": f"Day {seg['start']}-{seg['end']}",
            "place": seg["city"]
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()