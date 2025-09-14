import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def time_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def build_piecewise_int(index_var, values):
    # values: list of ints indexed by person id
    expr = IntVal(0)
    for i, v in enumerate(values):
        expr = If(index_var == i, IntVal(v), expr)
    return expr

def build_travel_from_start_expr(order_k, persons, distances, start_loc):
    expr = IntVal(0)
    for i, p in enumerate(persons):
        key = (start_loc, p["location"])
        expr = If(order_k == i, IntVal(distances.get(key, 0)), expr)
    return expr

def build_travel_between_expr(order_prev, order_cur, persons, distances):
    expr = IntVal(0)
    for i, pi in enumerate(persons):
        for j, pj in enumerate(persons):
            key = (pi["location"], pj["location"])
            expr = If(And(order_prev == i, order_cur == j), IntVal(distances.get(key, 0)), expr)
    return expr

def main():
    # Locations and travel times (minutes)
    locations = [
        "Haight-Ashbury",
        "Mission District",
        "Union Square",
        "Pacific Heights",
        "Bayview",
        "Fisherman's Wharf",
        "Marina District",
        "Richmond District",
        "Sunset District",
        "Golden Gate Park",
    ]

    # Distances dictionary
    d = {}
    # Haight-Ashbury
    d[("Haight-Ashbury","Mission District")] = 11
    d[("Haight-Ashbury","Union Square")] = 19
    d[("Haight-Ashbury","Pacific Heights")] = 12
    d[("Haight-Ashbury","Bayview")] = 18
    d[("Haight-Ashbury","Fisherman's Wharf")] = 23
    d[("Haight-Ashbury","Marina District")] = 17
    d[("Haight-Ashbury","Richmond District")] = 10
    d[("Haight-Ashbury","Sunset District")] = 15
    d[("Haight-Ashbury","Golden Gate Park")] = 7
    # Mission District
    d[("Mission District","Haight-Ashbury")] = 12
    d[("Mission District","Union Square")] = 15
    d[("Mission District","Pacific Heights")] = 16
    d[("Mission District","Bayview")] = 14
    d[("Mission District","Fisherman's Wharf")] = 22
    d[("Mission District","Marina District")] = 19
    d[("Mission District","Richmond District")] = 20
    d[("Mission District","Sunset District")] = 24
    d[("Mission District","Golden Gate Park")] = 17
    # Union Square
    d[("Union Square","Haight-Ashbury")] = 18
    d[("Union Square","Mission District")] = 14
    d[("Union Square","Pacific Heights")] = 15
    d[("Union Square","Bayview")] = 15
    d[("Union Square","Fisherman's Wharf")] = 15
    d[("Union Square","Marina District")] = 18
    d[("Union Square","Richmond District")] = 20
    d[("Union Square","Sunset District")] = 27
    d[("Union Square","Golden Gate Park")] = 22
    # Pacific Heights
    d[("Pacific Heights","Haight-Ashbury")] = 11
    d[("Pacific Heights","Mission District")] = 15
    d[("Pacific Heights","Union Square")] = 12
    d[("Pacific Heights","Bayview")] = 22
    d[("Pacific Heights","Fisherman's Wharf")] = 13
    d[("Pacific Heights","Marina District")] = 6
    d[("Pacific Heights","Richmond District")] = 12
    d[("Pacific Heights","Sunset District")] = 21
    d[("Pacific Heights","Golden Gate Park")] = 15
    # Bayview
    d[("Bayview","Haight-Ashbury")] = 19
    d[("Bayview","Mission District")] = 13
    d[("Bayview","Union Square")] = 18
    d[("Bayview","Pacific Heights")] = 23
    d[("Bayview","Fisherman's Wharf")] = 25
    d[("Bayview","Marina District")] = 27
    d[("Bayview","Richmond District")] = 25
    d[("Bayview","Sunset District")] = 23
    d[("Bayview","Golden Gate Park")] = 22
    # Fisherman's Wharf
    d[("Fisherman's Wharf","Haight-Ashbury")] = 22
    d[("Fisherman's Wharf","Mission District")] = 22
    d[("Fisherman's Wharf","Union Square")] = 13
    d[("Fisherman's Wharf","Pacific Heights")] = 12
    d[("Fisherman's Wharf","Bayview")] = 26
    d[("Fisherman's Wharf","Marina District")] = 9
    d[("Fisherman's Wharf","Richmond District")] = 18
    d[("Fisherman's Wharf","Sunset District")] = 27
    d[("Fisherman's Wharf","Golden Gate Park")] = 25
    # Marina District
    d[("Marina District","Haight-Ashbury")] = 16
    d[("Marina District","Mission District")] = 20
    d[("Marina District","Union Square")] = 16
    d[("Marina District","Pacific Heights")] = 7
    d[("Marina District","Bayview")] = 27
    d[("Marina District","Fisherman's Wharf")] = 10
    d[("Marina District","Richmond District")] = 11
    d[("Marina District","Sunset District")] = 19
    d[("Marina District","Golden Gate Park")] = 18
    # Richmond District
    d[("Richmond District","Haight-Ashbury")] = 10
    d[("Richmond District","Mission District")] = 20
    d[("Richmond District","Union Square")] = 21
    d[("Richmond District","Pacific Heights")] = 10
    d[("Richmond District","Bayview")] = 27
    d[("Richmond District","Fisherman's Wharf")] = 18
    d[("Richmond District","Marina District")] = 9
    d[("Richmond District","Sunset District")] = 11
    d[("Richmond District","Golden Gate Park")] = 9
    # Sunset District
    d[("Sunset District","Haight-Ashbury")] = 15
    d[("Sunset District","Mission District")] = 25
    d[("Sunset District","Union Square")] = 30
    d[("Sunset District","Pacific Heights")] = 21
    d[("Sunset District","Bayview")] = 22
    d[("Sunset District","Fisherman's Wharf")] = 29
    d[("Sunset District","Marina District")] = 21
    d[("Sunset District","Richmond District")] = 12
    d[("Sunset District","Golden Gate Park")] = 11
    # Golden Gate Park
    d[("Golden Gate Park","Haight-Ashbury")] = 7
    d[("Golden Gate Park","Mission District")] = 17
    d[("Golden Gate Park","Union Square")] = 22
    d[("Golden Gate Park","Pacific Heights")] = 16
    d[("Golden Gate Park","Bayview")] = 23
    d[("Golden Gate Park","Fisherman's Wharf")] = 24
    d[("Golden Gate Park","Marina District")] = 16
    d[("Golden Gate Park","Richmond District")] = 7
    d[("Golden Gate Park","Sunset District")] = 10

    # Add zero self-distances to avoid KeyError during expression construction
    for loc in locations:
        d[(loc, loc)] = 0

    # People with constraints
    persons = [
        {"name": "Elizabeth", "location": "Mission District", "start": minutes(10,30), "end": minutes(20,0), "min_duration": 90},
        {"name": "David", "location": "Union Square", "start": minutes(15,15), "end": minutes(19,0), "min_duration": 45},
        {"name": "Sandra", "location": "Pacific Heights", "start": minutes(7,0), "end": minutes(20,0), "min_duration": 120},
        {"name": "Thomas", "location": "Bayview", "start": minutes(19,30), "end": minutes(20,30), "min_duration": 30},
        {"name": "Robert", "location": "Fisherman's Wharf", "start": minutes(10,0), "end": minutes(15,0), "min_duration": 15},
        {"name": "Kenneth", "location": "Marina District", "start": minutes(10,45), "end": minutes(13,0), "min_duration": 45},
        {"name": "Melissa", "location": "Richmond District", "start": minutes(18,15), "end": minutes(20,0), "min_duration": 15},
        {"name": "Kimberly", "location": "Sunset District", "start": minutes(10,15), "end": minutes(18,15), "min_duration": 105},
        {"name": "Amanda", "location": "Golden Gate Park", "start": minutes(7,45), "end": minutes(18,45), "min_duration": 15},
    ]

    P = len(persons)
    start_location = "Haight-Ashbury"
    arrival_time_at_start = minutes(9, 0)

    opt = Optimize()
    opt.set(priority='lex')

    order = [Int(f"order_{k}") for k in range(P)]
    use = [Bool(f"use_{k}") for k in range(P)]
    start = [Int(f"start_{k}") for k in range(P)]
    end = [Int(f"end_{k}") for k in range(P)]

    # Domain constraints
    for k in range(P):
        opt.add(And(order[k] >= 0, order[k] < P))
        opt.add(Implies(use[k], And(start[k] >= 0, end[k] >= 0)))
    # All persons appear uniquely in order (permutation)
    opt.add(Distinct(order))

    # Monotonic use: used slots form an initial segment
    for k in range(1, P):
        opt.add(Implies(use[k], use[k-1]))

    # Piecewise data arrays
    durations = [p["min_duration"] for p in persons]
    avail_starts = [p["start"] for p in persons]
    avail_ends = [p["end"] for p in persons]

    # Meeting constraints per slot
    for k in range(P):
        dur_k = build_piecewise_int(order[k], durations)
        avs_k = build_piecewise_int(order[k], avail_starts)
        ave_k = build_piecewise_int(order[k], avail_ends)

        opt.add(Implies(use[k], end[k] == start[k] + dur_k))
        opt.add(Implies(use[k], start[k] >= avs_k))
        opt.add(Implies(use[k], end[k] <= ave_k))

    # Travel constraints from start to first meeting
    t0 = build_travel_from_start_expr(order[0], persons, d, start_location)
    opt.add(Implies(use[0], start[0] >= arrival_time_at_start + t0))

    # Travel constraints between consecutive used slots
    for k in range(1, P):
        t_between = build_travel_between_expr(order[k-1], order[k], persons, d)
        opt.add(Implies(And(use[k-1], use[k]), start[k] >= end[k-1] + t_between))

    # Objectives
    num_meetings = Sum([If(use[k], IntVal(1), IntVal(0)) for k in range(P)])
    last_end_terms = []
    for k in range(P):
        if k == P - 1:
            cond = use[k]
        else:
            cond = And(use[k], Not(use[k+1]))
        last_end_terms.append(If(cond, end[k], IntVal(0)))
    last_end = Sum(last_end_terms)

    h1 = opt.maximize(num_meetings)
    h2 = opt.minimize(last_end)

    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    model = opt.model()

    # Build itinerary
    result = {"itinerary": []}
    for k in range(P):
        if is_true(model.evaluate(use[k])):
            pid = model.evaluate(order[k]).as_long()
            person = persons[pid]
            s = model.evaluate(start[k]).as_long()
            e = model.evaluate(end[k]).as_long()
            result["itinerary"].append({
                "action": "meet",
                "location": person["location"],
                "person": person["name"],
                "start_time": time_to_str(s),
                "end_time": time_to_str(e)
            })

    print(json.dumps(result, indent=2))