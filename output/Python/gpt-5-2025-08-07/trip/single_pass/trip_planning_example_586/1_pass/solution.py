import json
import itertools
from collections import defaultdict

def compute_itinerary():
    # Input variables
    total_days = 12
    required_days = {
        "Frankfurt": 3,
        "Naples": 4,
        "Helsinki": 4,
        "Lyon": 3,
        "Prague": 2
    }
    # Direct flight graph (bidirectional)
    direct_flights = [
        ("Prague", "Lyon"),
        ("Prague", "Frankfurt"),
        ("Frankfurt", "Lyon"),
        ("Helsinki", "Naples"),
        ("Helsinki", "Frankfurt"),
        ("Naples", "Frankfurt"),
        ("Prague", "Helsinki"),
    ]
    # Must-attend windows (must be in these cities on these days)
    must_in_city_days = {
        "Helsinki": {2, 3, 4, 5},  # annual show
        "Prague": {1, 2},          # workshop
    }

    # Build adjacency set for constant time checks
    adjacency = set()
    for a, b in direct_flights:
        adjacency.add((a, b))
        adjacency.add((b, a))

    def has_direct(a, b):
        return (a, b) in adjacency

    # Pre-place mandatory segments based on constraints:
    # - Be in Prague on Days 1-2 (workshop on Day 1-2)
    # - Fly Prague -> Helsinki on Day 2 (counts for both)
    # - Be in Helsinki on Days 2-5 (show on Day 2-5)
    if not has_direct("Prague", "Helsinki"):
        raise ValueError("No direct flight Prague <-> Helsinki to satisfy Day 2 transfer.")

    fixed_segments = [
        ("Prague", 1, 2),
        ("Helsinki", 2, 5),
    ]

    remaining_cities = [c for c in required_days if c not in {"Prague", "Helsinki"}]

    solution_segments = None

    # Try permutations of the remaining cities to satisfy direct-flight path and day allocations
    for perm in itertools.permutations(remaining_cities):
        # Check direct flight chain: Helsinki -> perm[0] -> perm[1] -> perm[2]
        ok_links = has_direct("Helsinki", perm[0]) and all(has_direct(perm[i], perm[i+1]) for i in range(len(perm)-1))
        if not ok_links:
            continue

        # Construct segments:
        # Start the next city on Day 5 (arrival on Day 5 counts for both Helsinki and next city)
        segs = fixed_segments[:]
        current_start = 5
        for city in perm:
            duration = required_days[city]
            end_day = current_start + duration - 1
            segs.append((city, current_start, end_day))
            current_start = end_day  # next segment starts on the same day (flight overlap)

        # Validate day bounds and flight overlaps between segments
        if segs[0][1] != 1 or segs[-1][2] != total_days:
            continue

        valid = True
        # Validate direct flights on boundary days between consecutive segments
        for i in range(len(segs) - 1):
            city_a, start_a, end_a = segs[i]
            city_b, start_b, end_b = segs[i+1]
            if end_a != start_b:
                valid = False
                break
            if not has_direct(city_a, city_b):
                valid = False
                break
        if not valid:
            continue

        # Count days per city considering overlaps on flight days
        days_by_city = defaultdict(set)
        for city, start, end in segs:
            for d in range(start, end + 1):
                days_by_city[city].add(d)

        # Validate exact required days for each city
        if any(len(days_by_city[city]) != required_days[city] for city in required_days):
            continue

        # Validate presence in cities during must-attend windows
        if any(not must_days.issubset(days_by_city[city]) for city, must_days in must_in_city_days.items()):
            continue

        solution_segments = segs
        break

    if not solution_segments:
        raise ValueError("No valid itinerary found that satisfies all constraints.")

    # Prepare output itinerary
    itinerary = []
    for city, start, end in solution_segments:
        itinerary.append({"day_range": f"Day {start}-{end}", "place": city})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result))