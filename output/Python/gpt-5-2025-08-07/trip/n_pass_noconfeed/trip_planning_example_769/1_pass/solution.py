import itertools
import json

def build_adjacency(edges):
    adj = {}
    for a, b in edges:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    return adj

def compute_ranges(order, durations, total_days):
    # Day-sharing on flight days:
    # First city starts at Day 1, ends at 1 + dur - 1
    # Next city starts at previous end (shared flight day)
    ranges = []
    start = 1
    for city in order:
        end = start + durations[city] - 1
        ranges.append((city, start, end))
        start = end  # next segment shares this day
    # The last 'end' must equal total_days
    if ranges and ranges[-1][2] != total_days:
        return None
    return ranges

def has_direct_flights(order, adj):
    for i in range(len(order) - 1):
        if order[i+1] not in adj.get(order[i], set()):
            return False
    return True

def overlaps(a_start, a_end, b_start, b_end):
    return not (a_end < b_start or a_start > b_end)

def validate_constraints(ranges, constraints):
    # Unpack constraints
    ams_days = constraints["conference_amsterdam_days"]  # set of days
    reyk_window = constraints["reykjavik_window"]        # (start, end)
    munich_window = constraints["munich_window"]         # (start, end)

    # Map city -> (start, end)
    city_to_range = {city: (s, e) for city, s, e in ranges}

    # Amsterdam must include both conference days and total duration must be exact
    if "Amsterdam" not in city_to_range:
        return False
    a_start, a_end = city_to_range["Amsterdam"]
    # Conference days must both be in range
    if not (a_start <= 14 <= a_end and a_start <= 15 <= a_end):
        return False
    # Reykjavik window: at least one day overlap with window
    if "Reykjavik" not in city_to_range:
        return False
    r_start, r_end = city_to_range["Reykjavik"]
    if not overlaps(r_start, r_end, reyk_window[0], reyk_window[1]):
        return False
    # Munich window: at least one day overlap with window
    if "Munich" not in city_to_range:
        return False
    m_start, m_end = city_to_range["Munich"]
    if not overlaps(m_start, m_end, munich_window[0], munich_window[1]):
        return False

    return True

def main():
    # Input variables (trip constraints)
    total_days = 16
    durations = {
        "Porto": 5,
        "Prague": 4,
        "Reykjavik": 4,
        "Santorini": 2,
        "Amsterdam": 2,
        "Munich": 4,
    }
    cities = list(durations.keys())

    # Direct flight pairs (undirected)
    direct_flights = [
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
    adjacency = build_adjacency(direct_flights)

    # Event constraints
    constraints = {
        "reykjavik_window": (4, 7),      # must be in Reykjavik at least one day within this window
        "munich_window": (7, 10),        # must be in Munich at least one day within this window
        "conference_amsterdam_days": {14, 15},  # must be in Amsterdam both days 14 and 15
    }

    # Sanity check: sum durations minus number of transitions must equal total_days
    required_unique_days = sum(durations.values()) - (len(cities) - 1)
    if required_unique_days != total_days:
        # No feasible solution under day-sharing model
        print(json.dumps({"itinerary": []}))
        return

    found = None
    # Search permutations for a feasible route satisfying direct flights and day constraints
    for order in itertools.permutations(cities):
        # Ensure all cities are visited exactly once (by construction of permutations)
        # Check direct flight feasibility between consecutive cities
        if not has_direct_flights(order, adjacency):
            continue

        # Compute day ranges with shared flight days
        ranges = compute_ranges(order, durations, total_days)
        if ranges is None:
            continue

        # Validate all special constraints
        if not validate_constraints(ranges, constraints):
            continue

        # Feasible itinerary found
        found = ranges
        break

    if not found:
        print(json.dumps({"itinerary": []}))
        return

    # Format output
    itinerary = []
    for city, start, end in found:
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()