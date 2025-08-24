import json
from collections import defaultdict

def build_adjacency():
    adj = defaultdict(set)

    def add_bidir(a, b):
        adj[a].add(b)
        adj[b].add(a)

    def add_oneway(a, b):
        adj[a].add(b)

    # Direct flights (bi-directional when "and", one-way when "from X to Y")
    add_bidir("Dublin", "Brussels")
    add_bidir("Mykonos", "Naples")
    add_bidir("Venice", "Istanbul")
    add_bidir("Frankfurt", "Krakow")
    add_bidir("Naples", "Dublin")
    add_bidir("Krakow", "Brussels")
    add_bidir("Naples", "Istanbul")
    add_bidir("Naples", "Brussels")
    add_bidir("Istanbul", "Frankfurt")
    add_oneway("Brussels", "Frankfurt")  # one-way
    add_bidir("Istanbul", "Krakow")
    add_bidir("Istanbul", "Brussels")
    add_bidir("Venice", "Frankfurt")
    add_bidir("Naples", "Frankfurt")
    add_bidir("Dublin", "Krakow")
    add_bidir("Venice", "Brussels")
    add_bidir("Naples", "Venice")
    add_bidir("Istanbul", "Dublin")
    add_bidir("Venice", "Dublin")
    add_bidir("Dublin", "Frankfurt")

    return adj

def compute_intervals(order, durations):
    intervals = {}
    if not order:
        return intervals
    # Start at Day 1 for the first city
    start = 1
    end = start + durations[order[0]] - 1
    intervals[order[0]] = (start, end)
    for i in range(1, len(order)):
        # Next city's start = previous city's end (overlap travel day)
        start = intervals[order[i - 1]][1]
        end = start + durations[order[i]] - 1
        intervals[order[i]] = (start, end)
    return intervals

def intersects(a, b):
    # a and b are tuples (s, e); return True if they overlap
    return not (a[1] < b[0] or b[1] < a[0])

def equals_interval(a, b):
    return a[0] == b[0] and a[1] == b[1]

def valid_prefix_constraints(order, intervals, exact_constraints, intersect_constraints):
    # Check constraints only for cities present in intervals so far
    for city, fixed in exact_constraints.items():
        if city in intervals:
            if not equals_interval(intervals[city], fixed):
                return False
    for city, win in intersect_constraints.items():
        if city in intervals:
            if not intersects(intervals[city], win):
                return False
    return True

def search_itinerary(cities, durations, adj, total_days, exact_constraints, intersect_constraints):
    # Start must be Mykonos to satisfy "between day 1 and day 4" for 4 days
    start_city = "Mykonos"
    if start_city not in cities:
        return None

    def dfs(path):
        # Compute current intervals for the placed path
        intervals = compute_intervals(path, durations)

        # Early pruning: if any interval exceeds total_days or invalid ranges
        for c, (s, e) in intervals.items():
            if s < 1 or e > total_days:
                return None

        # Check prefix constraints
        if not valid_prefix_constraints(path, intervals, exact_constraints, intersect_constraints):
            return None

        # If complete path includes all cities, verify final consistency
        if len(path) == len(cities):
            # Verify all consecutive edges are valid direct flights
            for i in range(len(path) - 1):
                if path[i+1] not in adj[path[i]]:
                    return None
            # Ensure union of days equals total_days (implicit with overlaps and start at Day 1)
            # Verify final day ends at total_days
            last_city = path[-1]
            if intervals[last_city][1] != total_days:
                return None
            # Final validation: all constraints must hold
            for city, fixed in exact_constraints.items():
                if city not in intervals or not equals_interval(intervals[city], fixed):
                    return None
            for city, win in intersect_constraints.items():
                if city not in intervals or not intersects(intervals[city], win):
                    return None
            return intervals

        # Try to extend the path
        last = path[-1]
        remaining = [c for c in cities if c not in path]

        for nxt in remaining:
            if nxt in adj[last]:
                res = dfs(path + [nxt])
                if res is not None:
                    return res
        return None

    return dfs([start_city])

def main():
    total_days = 21
    cities = [
        "Dublin",
        "Krakow",
        "Istanbul",
        "Venice",
        "Naples",
        "Brussels",
        "Mykonos",
        "Frankfurt",
    ]
    durations = {
        "Dublin": 5,
        "Krakow": 4,
        "Istanbul": 3,
        "Venice": 3,
        "Naples": 4,
        "Brussels": 2,
        "Mykonos": 4,
        "Frankfurt": 3,
    }

    # Constraints
    # Exact windows (must match exactly these day ranges)
    exact_constraints = {
        "Dublin": (11, 15),   # Attend show for all 5 days in Dublin
        "Mykonos": (1, 4),    # Visit relatives between Day 1-4, staying 4 days means exactly days 1-4
    }

    # Intersect windows (must be present at least one day within these ranges)
    intersect_constraints = {
        "Istanbul": (9, 11),   # Meet a friend between Day 9-11
        "Frankfurt": (15, 17), # Tour with friends between Day 15-17
    }

    adj = build_adjacency()

    # Verify day sum logic: sum(durations) - (num_transitions) must equal total_days
    sum_days = sum(durations.values())
    num_transitions = len(cities) - 1
    if sum_days - num_transitions != total_days:
        raise ValueError("Inconsistent total days with city durations and transitions.")

    intervals = search_itinerary(cities, durations, adj, total_days, exact_constraints, intersect_constraints)
    if intervals is None:
        raise RuntimeError("No feasible itinerary found with given constraints.")

    # Build itinerary in chronological order
    itinerary_items = sorted(((city, rng) for city, rng in intervals.items()), key=lambda x: x[1][0])
    itinerary = [{"day_range": f"Day {rng[0]}-{rng[1]}", "place": city} for city, rng in itinerary_items]

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()