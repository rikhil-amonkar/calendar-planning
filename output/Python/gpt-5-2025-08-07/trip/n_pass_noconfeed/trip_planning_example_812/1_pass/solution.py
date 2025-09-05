import json
from itertools import permutations

def build_adjacency(edges_bi, edges_dir):
    adj = {}
    def add_edge(a,b):
        adj.setdefault(a, set()).add(b)
    for a,b in edges_bi:
        add_edge(a,b)
        add_edge(b,a)
    for a,b in edges_dir:
        add_edge(a,b)
    return adj

def compute_itinerary(cities_duration, events, edges_bi, edges_dir, total_days):
    # Build flight adjacency (direct flights only)
    adj = build_adjacency(edges_bi, edges_dir)

    # Ensure we have exactly 7 cities (as per requirement)
    cities = list(cities_duration.keys())
    assert len(cities) == 7, "Expected exactly 7 cities."

    # Deduce fixed positioning from anchored events:
    # - Porto must include day 1, so Porto must start at day 1 => first segment
    # - Vienna must include day 20 and 19 with duration 2 => must start day 19 => last segment
    # The rest will be permuted in the middle.
    first_city = "Porto"
    last_city = "Vienna"
    assert first_city in cities and last_city in cities

    middle_cities = [c for c in cities if c not in (first_city, last_city)]

    # Helper to check direct flight between consecutive cities
    def has_direct_flights(seq):
        for a, b in zip(seq[:-1], seq[1:]):
            if b not in adj.get(a, set()):
                return False
        return True

    # For a sequence of cities, compute day ranges considering overlap rule:
    # Segment i: start_i = end_{i-1}, end_i = start_i + dur - 1; start_1 = 1
    def compute_ranges(seq):
        ranges = []
        start = 1
        for city in seq:
            dur = cities_duration[city]
            end = start + dur - 1
            ranges.append((city, start, end))
            start = end  # next segment starts on previous segment's end day (overlap travel day)
        return ranges

    # Check that all anchored event days are within the city's allocated range
    def events_ok(ranges):
        by_city = {city: (s, e) for city, s, e in ranges}
        for city, (req_s, req_e) in events.items():
            if city not in by_city:
                return False
            s, e = by_city[city]
            if not (s <= req_s and e >= req_e):
                return False
        return True

    # Check total calendar coverage equals total_days
    def calendar_days_ok(ranges):
        # With overlap rule: calendar_days = sum(durations) - (segments - 1)
        sum_durations = sum(cities_duration[c] for c, _, _ in ranges)
        segments = len(ranges)
        return (sum_durations - (segments - 1)) == total_days

    # Search all permutations of middle cities to find a valid sequence
    for perm in permutations(middle_cities):
        seq = [first_city] + list(perm) + [last_city]
        # Check direct flights
        if not has_direct_flights(seq):
            continue
        # Compute ranges
        ranges = compute_ranges(seq)
        # End of last segment must be exactly total_days
        if ranges[-1][2] != total_days:
            continue
        # Check event coverage
        if not events_ok(ranges):
            continue
        # Check calendar coverage
        if not calendar_days_ok(ranges):
            continue
        # Found a valid itinerary
        itinerary = []
        for city, s, e in ranges:
            itinerary.append({
                "day_range": f"Day {s}-{e}",
                "place": city
            })
        return {"itinerary": itinerary}

    # If no exact solution, return empty itinerary (should not happen for given constraints)
    return {"itinerary": []}

def main():
    # Input variables (trip constraints)
    cities_duration = {
        "Paris": 5,
        "Florence": 3,
        "Vienna": 2,
        "Porto": 3,
        "Munich": 5,
        "Nice": 5,
        "Warsaw": 3
    }
    # Anchored events: must be in city for all days in inclusive range
    events = {
        "Porto": (1, 3),    # Workshop days 1-3
        "Warsaw": (13, 15), # Wedding days 13-15
        "Vienna": (19, 20)  # Relatives days 19-20
    }
    total_days = 20

    # Direct flight definitions
    edges_bi = [
        ("Florence", "Vienna"),
        ("Paris", "Warsaw"),
        ("Munich", "Vienna"),
        ("Porto", "Vienna"),
        ("Warsaw", "Vienna"),
        ("Munich", "Warsaw"),
        ("Munich", "Nice"),
        ("Paris", "Florence"),
        ("Warsaw", "Nice"),
        ("Porto", "Munich"),
        ("Porto", "Nice"),
        ("Paris", "Vienna"),
        ("Nice", "Vienna"),
        ("Porto", "Paris"),
        ("Paris", "Nice"),
        ("Paris", "Munich"),
        ("Porto", "Warsaw"),
    ]
    edges_dir = [
        ("Florence", "Munich"),  # Directed flight
    ]

    result = compute_itinerary(cities_duration, events, edges_bi, edges_dir, total_days)
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()