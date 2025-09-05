import itertools
import json

def build_adjacency(flight_descriptions):
    adjacency = {}
    def add_edge(a, b):
        adjacency.setdefault(a, set()).add(b)
        adjacency.setdefault(b, set())  # ensure node exists

    for desc in flight_descriptions:
        s = desc.strip()
        if s.startswith("from "):
            # format: from A to B
            rest = s[len("from "):]
            if " to " in rest:
                a, b = rest.split(" to ", 1)
                a, b = a.strip(), b.strip()
                adjacency.setdefault(a, set()).add(b)
                adjacency.setdefault(b, set())
        elif " and " in s:
            a, b = s.split(" and ")
            a, b = a.strip(), b.strip()
            add_edge(a, b)
            add_edge(b, a)
        else:
            # Skip malformed entries
            pass
    return adjacency

def compute_day_ranges(order, durations, start_day=1):
    ranges = {}
    current_start = start_day
    for city in order:
        duration = durations[city]
        end_day = current_start + duration - 1
        ranges[city] = (current_start, end_day)
        current_start = end_day  # overlap day: fly on end_day
    return ranges

def valid_event_windows(ranges, required_windows):
    for city, (req_start, req_end) in required_windows.items():
        s, e = ranges[city]
        if not (s <= req_start and e >= req_end):
            return False
    return True

def path_has_direct_flights(order, adjacency):
    for a, b in zip(order[:-1], order[1:]):
        if b not in adjacency.get(a, set()):
            return False
    return True

def main():
    # Trip constraints
    total_days = 22
    durations = {
        "Brussels": 3,
        "Helsinki": 3,
        "Split": 4,
        "Dubrovnik": 2,
        "Istanbul": 5,
        "Milan": 4,
        "Vilnius": 5,
        "Frankfurt": 3,
    }
    # Required presence windows (inclusive)
    required_windows = {
        "Istanbul": (1, 5),   # Annual show
        "Frankfurt": (16, 18),# Wedding
        "Vilnius": (18, 22),  # Workshop
    }

    # Flight connectivity descriptions
    flight_descriptions = [
        "Milan and Frankfurt",
        "Split and Frankfurt",
        "Milan and Split",
        "Brussels and Vilnius",
        "Brussels and Helsinki",
        "Istanbul and Brussels",
        "Milan and Vilnius",
        "Brussels and Milan",
        "Istanbul and Helsinki",
        "Helsinki and Vilnius",
        "Helsinki and Dubrovnik",
        "Split and Vilnius",
        "from Dubrovnik to Istanbul",
        "Istanbul and Milan",
        "Helsinki and Frankfurt",
        "Istanbul and Vilnius",
        "Split and Helsinki",
        "Milan and Helsinki",
        "Istanbul and Frankfurt",
        "from Brussels to Frankfurt",
        "Dubrovnik and Frankfurt",
        "Frankfurt and Vilnius",
    ]
    adjacency = build_adjacency(flight_descriptions)

    # Establish ordered search: Fix Istanbul first, Frankfurt second-last, Vilnius last
    start_city = "Istanbul"
    penultimate_city = "Frankfurt"
    end_city = "Vilnius"

    all_cities = list(durations.keys())
    middle_cities = sorted([c for c in all_cities if c not in {start_city, penultimate_city, end_city}])

    found_order = None
    found_ranges = None

    for perm in itertools.permutations(middle_cities):
        candidate_order = [start_city] + list(perm) + [penultimate_city, end_city]

        # Check direct flights between each consecutive pair
        if not path_has_direct_flights(candidate_order, adjacency):
            continue

        # Compute day ranges with overlap flights on transition days
        ranges = compute_day_ranges(candidate_order, durations, start_day=1)
        # Validate end day equals total_days
        if ranges[candidate_order[-1]][1] != total_days:
            continue

        # Validate required windows
        if not valid_event_windows(ranges, required_windows):
            continue

        # All constraints satisfied
        found_order = candidate_order
        found_ranges = ranges
        break

    if not found_order:
        # If no valid itinerary is found, output an empty structure (should not happen with given inputs)
        print(json.dumps({"itinerary": []}, ensure_ascii=False))
        return

    itinerary = []
    for city in found_order:
        s, e = found_ranges[city]
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()