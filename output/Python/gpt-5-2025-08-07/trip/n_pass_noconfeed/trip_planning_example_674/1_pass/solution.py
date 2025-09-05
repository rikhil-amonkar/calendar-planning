import json
from itertools import permutations

def build_adjacency(flight_descriptions):
    adj = {}
    def add_edge(a, b):
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set())  # ensure key exists

    for desc in flight_descriptions:
        s = desc.strip().rstrip(".")
        if " and " in s:
            a, b = [x.strip() for x in s.split(" and ")]
            add_edge(a, b)
            add_edge(b, a)
        elif s.lower().startswith("from "):
            # format: from X to Y
            s2 = s[5:]  # remove "from "
            if " to " not in s2:
                continue
            a, b = [x.strip() for x in s2.split(" to ")]
            adj.setdefault(a, set()).add(b)
            adj.setdefault(b, set())
        else:
            # ignore malformed
            pass
    return adj

def compute_ranges(order, desired_days):
    ranges = {}
    start = 1
    for city in order:
        end = start + desired_days[city] - 1
        ranges[city] = (start, end)
        start = end  # next segment starts on the same day (flight day counts twice)
    return ranges

def windows_satisfied(ranges, windows):
    for city, (a, b) in windows.items():
        rs, re = ranges[city]
        if not (rs <= a and re >= b):
            return False
    return True

def adjacency_ok(order, adj):
    for i in range(len(order) - 1):
        a, b = order[i], order[i+1]
        if a not in adj or b not in adj[a]:
            return False
    return True

def solve_itinerary():
    total_days = 14
    cities = ["Helsinki", "Warsaw", "Madrid", "Split", "Reykjavik", "Budapest"]

    # Desired days in each city
    desired_days = {
        "Helsinki": 2,
        "Warsaw": 3,
        "Madrid": 4,
        "Split": 4,
        "Reykjavik": 2,
        "Budapest": 4,
    }

    # Must-be-present windows (inclusive)
    windows = {
        "Helsinki": (1, 2),      # workshop between day 1 and 2
        "Reykjavik": (8, 9),     # meet friend between day 8 and 9
        "Warsaw": (9, 11),       # visit relatives between day 9 and 11
    }

    flight_descriptions = [
        "Helsinki and Reykjavik",
        "Budapest and Warsaw",
        "Madrid and Split",
        "Helsinki and Split",
        "Helsinki and Madrid",
        "Helsinki and Budapest",
        "Reykjavik and Warsaw",
        "Helsinki and Warsaw",
        "Madrid and Budapest",
        "Budapest and Reykjavik",
        "Madrid and Warsaw",
        "Warsaw and Split",
        "from Reykjavik to Madrid",
    ]
    adj = build_adjacency(flight_descriptions)

    n_cities = len(cities)
    # Validate the overlap feasibility: sum(desired) must equal total_days + (n_cities - 1)
    sum_desired = sum(desired_days[c] for c in cities)
    required_sum = total_days + (n_cities - 1)
    if sum_desired != required_sum:
        raise ValueError(f"Infeasible day totals: sum(desired)={sum_desired} must equal {required_sum}.")

    start_city = "Helsinki"
    others = [c for c in cities if c != start_city]

    best_order = None
    for perm in permutations(others):
        order = [start_city] + list(perm)

        # Connectivity constraint: only direct flights between successive cities
        if not adjacency_ok(order, adj):
            continue

        # Compute day ranges based on desired lengths with 1-day overlaps at transitions
        ranges = compute_ranges(order, desired_days)

        # Validate total timeline ends exactly on total_days
        last_end = ranges[order[-1]][1]
        if last_end != total_days:
            continue

        # Check presence windows
        if not windows_satisfied(ranges, windows):
            continue

        # Found a feasible order
        best_order = order
        best_ranges = ranges
        break

    if not best_order:
        raise RuntimeError("No feasible itinerary found that satisfies all constraints.")

    itinerary = []
    for city in best_order:
        s, e = best_ranges[city]
        itinerary.append({"day_range": f"Day {s}-{e}", "place": city})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, ensure_ascii=False))