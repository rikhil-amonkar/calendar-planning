# Solve the scheduling problem with Z3 to maximize the number of friends met
# and produce a JSON itinerary.

from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum
import json

def minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def fmt_time(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def solve():
    # Locations and travel times (in minutes)
    T = {
        "Bayview": {
            "Russian Hill": 23,
            "Alamo Square": 16,
            "North Beach": 21,
            "Financial District": 19,
        },
        "Russian Hill": {
            "Bayview": 23,
            "Alamo Square": 15,
            "North Beach": 5,
            "Financial District": 11,
        },
        "Alamo Square": {
            "Bayview": 16,
            "Russian Hill": 13,
            "North Beach": 15,
            "Financial District": 17,
        },
        "North Beach": {
            "Bayview": 22,
            "Russian Hill": 4,
            "Alamo Square": 16,
            "Financial District": 8,
        },
        "Financial District": {
            "Bayview": 19,
            "Russian Hill": 10,
            "Alamo Square": 17,
            "North Beach": 7,
        },
    }

    # People: name, location, availability window [start, end], minimum meeting duration
    people = [
        {"name": "Joseph",  "loc": "Russian Hill",      "win": (minutes("08:30"), minutes("19:15")), "min": 60},
        {"name": "Nancy",   "loc": "Alamo Square",      "win": (minutes("11:00"), minutes("16:00")), "min": 90},
        {"name": "Jason",   "loc": "North Beach",       "win": (minutes("16:45"), minutes("21:45")), "min": 15},
        {"name": "Jeffrey", "loc": "Financial District","win": (minutes("10:30"), minutes("15:45")), "min": 45},
    ]

    origin_loc = "Bayview"
    origin_time = minutes("09:00")
    day_end = minutes("23:59")

    n = len(people)

    opt = Optimize()

    # Decision variables
    s = [Int(f"s_{i}") for i in range(n)]   # start time (minutes)
    d = [Int(f"d_{i}") for i in range(n)]   # duration (minutes)
    x = [Bool(f"x_{i}") for i in range(n)]  # meet this person?
    # Pairwise ordering variable: i before j
    b = {}
    for i in range(n):
        for j in range(i+1, n):
            b[(i, j)] = Bool(f"b_{i}_{j}")

    # Bounds and window constraints
    for i, p in enumerate(people):
        w_start, w_end = p["win"]
        min_d = p["min"]
        # Basic bounds
        opt.add(s[i] >= 0, s[i] <= day_end)
        opt.add(d[i] >= 0)
        # If meeting occurs, enforce window and minimum duration
        opt.add(And(x[i], True) == x[i])  # ensure proper boolean
        opt.add(Implies(x[i], And(s[i] >= w_start, s[i] + d[i] <= w_end, d[i] >= min_d)))
        # If not meeting, duration is zero (fix start to 0 to avoid dangling values)
        opt.add(Implies(Not(x[i]), And(d[i] == 0, s[i] == 0)))
        # Reachability from origin (can always wait at destination)
        opt.add(Implies(x[i], s[i] >= origin_time + T[origin_loc][p["loc"]]))

    # Disjunctive non-overlap and travel-time constraints between meetings
    for i in range(n):
        for j in range(i+1, n):
            li, lj = people[i]["loc"], people[j]["loc"]
            tij = T[li][lj]
            tji = T[lj][li]
            bij = b[(i, j)]
            # If both meetings occur and i is before j
            opt.add(Implies(And(x[i], x[j], bij), s[j] >= s[i] + d[i] + tij))
            # If both meetings occur and j is before i
            opt.add(Implies(And(x[i], x[j], Not(bij)), s[i] >= s[j] + d[j] + tji))
            # If at least one meeting does not occur, no ordering constraint is necessary (already gated above)

    # Objective 1: maximize number of friends met
    meet_count_terms = [If(x[i], 1, 0) for i in range(n)]
    opt.maximize(Sum(meet_count_terms))

    # Objective 2: maximize total meeting time (reduces idle waiting between feasible meetings)
    opt.maximize(Sum(d))

    # Solve
    if opt.check() not in (1,):
        raise RuntimeError("No solution found")

    m = opt.model()

    # Extract itinerary: meetings sorted by start time
    schedule = []
    for i, p in enumerate(people):
        if m.eval(x[i]):
            si = m.eval(s[i]).as_long()
            di = m.eval(d[i]).as_long()
            ei = si + di
            schedule.append({
                "action": "meet",
                "person": p["name"],
                "start_time": fmt_time(si),
                "end_time": fmt_time(ei)
            })
    schedule.sort(key=lambda e: minutes(e["start_time"]))

    return {"itinerary": schedule}

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result))