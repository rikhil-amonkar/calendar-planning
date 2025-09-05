import itertools
import json

def build_adjacency(edges):
    adj = set()
    for a, b in edges:
        adj.add(frozenset((a, b)))
    return adj

def has_direct_flight(a, b, adj):
    return frozenset((a, b)) in adj

def compute_ranges(order, durations, total_days):
    # Following the rule: if you travel on day X from city A to B, both cities count day X.
    # We model segments as inclusive ranges with overlaps at boundaries.
    ranges = {}
    prev_end = None
    for i, city in enumerate(order):
        L = durations[city]
        if i == 0:
            start = 1
            end = L
        else:
            start = prev_end  # overlap on boundary day
            end = prev_end + L - 1
        ranges[city] = (start, end)
        prev_end = end
    # Validate last day ends at total_days
    if prev_end != total_days:
        return None
    return ranges

def days_in_range(start, end):
    return set(range(start, end + 1))

def intersects_days(r, day_set):
    s, e = r
    return len(days_in_range(s, e).intersection(day_set)) > 0

def meets_all_constraints(order, ranges, constraints, adj):
    # Direct flight constraints
    for i in range(len(order) - 1):
        if not has_direct_flight(order[i], order[i + 1], adj):
            return False

    # Barcelona show: must be in Barcelona on days 1-3 (Barcelona duration is 3 days)
    bcn_range = ranges["Barcelona"]
    if bcn_range != (1, 3):
        return False

    # Oslo: visit for 2 days and meet friends between day 3 and day 4 (be there both days)
    osl_range = ranges["Oslo"]
    if not ({3, 4}).issubset(days_in_range(*osl_range)):
        return False

    # Brussels: visit for 3 days and meet a friend between day 9 and 11 (at least one day)
    bru_range = ranges["Brussels"]
    if not intersects_days(bru_range, set(range(9, 12))):  # 9,10,11
        return False

    # Duration checks implicitly satisfied by construction, but validate anyway
    for city, dur in constraints["durations"].items():
        s, e = ranges[city]
        if (e - s + 1) != dur:
            return False

    return True

def objective_for_brussels(ranges):
    # Prefer meeting as close as possible to day 10 within the 9-11 window.
    bru_s, bru_e = ranges["Brussels"]
    candidates = [d for d in range(bru_s, bru_e + 1) if 9 <= d <= 11]
    if not candidates:
        return (float('inf'), float('inf'))  # invalid
    best_dist = min(abs(d - 10) for d in candidates)
    earliest_meet = min(candidates)
    # Objective: minimize (distance to day10, earliest meeting day), then tie-break by Brussels start
    return (best_dist, earliest_meet)

def plan_itinerary():
    total_days = 16
    cities = ["Barcelona", "Oslo", "Venice", "Split", "Brussels", "Copenhagen", "Stuttgart"]

    durations = {
        "Oslo": 2,
        "Stuttgart": 3,
        "Venice": 4,
        "Split": 4,
        "Barcelona": 3,
        "Brussels": 3,
        "Copenhagen": 3,
    }

    # Direct flights (undirected)
    direct_edges = [
        ("Venice", "Stuttgart"),
        ("Oslo", "Brussels"),
        ("Split", "Copenhagen"),
        ("Barcelona", "Copenhagen"),
        ("Barcelona", "Venice"),
        ("Brussels", "Venice"),
        ("Barcelona", "Stuttgart"),
        ("Copenhagen", "Brussels"),
        ("Oslo", "Split"),
        ("Oslo", "Venice"),
        ("Barcelona", "Split"),
        ("Oslo", "Copenhagen"),
        ("Barcelona", "Oslo"),
        ("Copenhagen", "Stuttgart"),
        ("Split", "Stuttgart"),
        ("Copenhagen", "Venice"),
        ("Barcelona", "Brussels"),
    ]
    adj = build_adjacency(direct_edges)

    # Feasibility check: Sum of durations = total_days + (number_of_cities - 1)
    if sum(durations[c] for c in cities) != total_days + (len(cities) - 1):
        raise ValueError("Infeasible duration totals given the overlap rule and total days.")

    constraints = {
        "total_days": total_days,
        "durations": durations,
        "windows": {
            "barcelona_show": (1, 3),
            "oslo_meet": {3, 4},
            "brussels_meet_window": (9, 11),
        }
    }

    # Barcelona must be first to be there for days 1-3; Oslo must be second to include days 3 and 4.
    start_order = ["Barcelona", "Oslo"]
    remaining = [c for c in cities if c not in start_order]

    best_order = None
    best_ranges = None
    best_obj = (float('inf'), float('inf'))

    # Try all permutations of the remaining cities
    for perm in itertools.permutations(sorted(remaining)):
        order = start_order + list(perm)

        # Quick adjacency pruning: check direct flights across the chain before heavy checks
        feasible_chain = True
        for i in range(len(order) - 1):
            if not has_direct_flight(order[i], order[i + 1], adj):
                feasible_chain = False
                break
        if not feasible_chain:
            continue

        ranges = compute_ranges(order, durations, total_days)
        if ranges is None:
            continue

        if not meets_all_constraints(order, ranges, constraints, adj):
            continue

        obj = objective_for_brussels(ranges)
        # Tie-break by lexicographic order of the full order if objectives equal
        if obj < best_obj or (obj == best_obj and (best_order is None or tuple(order) < tuple(best_order))):
            best_obj = obj
            best_order = order
            best_ranges = ranges

    if not best_order:
        result = {
            "error": "No valid itinerary found under the given constraints."
        }
        print(json.dumps(result))
        return

    # Build itinerary list
    itinerary = []
    for city in best_order:
        s, e = best_ranges[city]
        itinerary.append({"day_range": f"Day {s}-{e}", "place": city})

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    plan_itinerary()