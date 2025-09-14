import json
from z3 import *

def to_minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def solve_itinerary():
    # Locations
    RICHMOND = "Richmond District"
    MARINA = "Marina District"
    CHINATOWN = "Chinatown"
    FINANCIAL = "Financial District"
    BAYVIEW = "Bayview"
    UNION_SQ = "Union Square"

    # Travel times (directed, in minutes)
    travel = {
        RICHMOND: {MARINA: 9, CHINATOWN: 20, FINANCIAL: 22, BAYVIEW: 26, UNION_SQ: 21},
        MARINA: {RICHMOND: 11, CHINATOWN: 16, FINANCIAL: 17, BAYVIEW: 27, UNION_SQ: 16},
        CHINATOWN: {RICHMOND: 20, MARINA: 12, FINANCIAL: 5, BAYVIEW: 22, UNION_SQ: 7},
        FINANCIAL: {RICHMOND: 21, MARINA: 15, CHINATOWN: 5, BAYVIEW: 19, UNION_SQ: 9},
        BAYVIEW: {RICHMOND: 25, MARINA: 25, CHINATOWN: 18, FINANCIAL: 19, UNION_SQ: 17},
        UNION_SQ: {RICHMOND: 20, MARINA: 18, CHINATOWN: 7, FINANCIAL: 9, BAYVIEW: 15},
    }

    # Friends data
    # 0: Kimberly (Marina) [13:15-16:45], min 15
    # 1: Robert (Chinatown) [12:15-20:15], min 15
    # 2: Rebecca (Financial) [13:15-16:45], min 75
    # 3: Margaret (Bayview) [9:30-13:30], min 30
    # 4: Kenneth (Union Square) [19:30-21:15], min 75
    friends = [
        {"name": "Kimberly", "location": MARINA, "start": to_minutes(13, 15), "end": to_minutes(16, 45), "min_dur": 15},
        {"name": "Robert", "location": CHINATOWN, "start": to_minutes(12, 15), "end": to_minutes(20, 15), "min_dur": 15},
        {"name": "Rebecca", "location": FINANCIAL, "start": to_minutes(13, 15), "end": to_minutes(16, 45), "min_dur": 75},
        {"name": "Margaret", "location": BAYVIEW, "start": to_minutes(9, 30), "end": to_minutes(13, 30), "min_dur": 30},
        {"name": "Kenneth", "location": UNION_SQ, "start": to_minutes(19, 30), "end": to_minutes(21, 15), "min_dur": 75},
    ]

    n = len(friends)
    NONE = n  # sentinel for unused order positions

    # Z3 variables
    o = Optimize()

    order = [Int(f"order_{k}") for k in range(n)]
    start = [Int(f"start_{i}") for i in range(n)]
    end = [Int(f"end_{i}") for i in range(n)]
    meet = [Bool(f"meet_{i}") for i in range(n)]

    # Domain constraints
    for k in range(n):
        o.add(order[k] >= 0, order[k] <= NONE)
    for i in range(n):
        o.add(start[i] >= 0, start[i] <= 24 * 60)
        o.add(end[i] >= 0, end[i] <= 24 * 60)

    # Once NONE appears in the order, all subsequent must be NONE
    for k in range(1, n):
        o.add(Implies(order[k - 1] == NONE, order[k] == NONE))

    # Distinctness among non-NONE order entries
    for i in range(n):
        for j in range(i + 1, n):
            o.add(Implies(And(order[i] != NONE, order[j] != NONE), order[i] != order[j]))

    # Meet equivalence: meet[i] <-> appears in order
    for i in range(n):
        o.add(meet[i] == Or(*[order[k] == i for k in range(n)]))

    # Availability and duration constraints when meeting
    for i, f in enumerate(friends):
        o.add(Implies(meet[i], And(
            start[i] >= f["start"],
            end[i] <= f["end"],
            end[i] - start[i] >= f["min_dur"]
        )))

    # Start location and time
    arrive_richmond = to_minutes(9, 0)

    # Travel constraints based on order positions
    # For first meeting: from Richmond at 9:00 with travel time
    for i, f in enumerate(friends):
        o.add(Implies(order[0] == i, start[i] >= arrive_richmond + travel[RICHMOND][f["location"]]))

    # For subsequent meetings: ensure travel time between consecutive meetings
    for k in range(1, n):
        for i in range(n):
            for j in range(n):
                loc_i = friends[i]["location"]
                loc_j = friends[j]["location"]
                o.add(Implies(And(order[k] == i, order[k - 1] == j),
                              end[j] + travel[loc_j][loc_i] <= start[i]))

    # Objective: maximize number of meetings
    total_meetings = Sum([If(meet[i], 1, 0) for i in range(n)])
    o.maximize(total_meetings)

    # Secondary objective: minimize total end time (encourages tighter/earlier schedule)
    total_end = Sum([If(meet[i], end[i], 0) for i in range(n)])
    o.minimize(total_end)

    # Solve
    if o.check() != sat:
        return []

    m = o.model()

    # Build itinerary in order
    itinerary = []
    for k in range(n):
        idx = m.eval(order[k]).as_long()
        if idx == NONE:
            break
        s = m.eval(start[idx]).as_long()
        e = m.eval(end[idx]).as_long()
        itinerary.append({
            "action": "meet",
            "location": friends[idx]["location"],
            "person": friends[idx]["name"],
            "start_time": fmt_time(s),
            "end_time": fmt_time(e),
        })

    return itinerary

if __name__ == "__main__":
    itinerary = solve_itinerary()
    print("SOLUTION:" + json.dumps({"itinerary": itinerary}, ensure_ascii=False))