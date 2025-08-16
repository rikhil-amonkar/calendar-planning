# Requires z3-solver package: pip install z3-solver
from z3 import Optimize, Int, Bool, If, And, Not, Implies, Sum
import json

def to_minutes(hhmm):
    hh, mm = map(int, hhmm.split(":"))
    return hh * 60 + mm

def fmt_time(m):
    hh = m // 60
    mm = m % 60
    return f"{hh:02d}:{mm:02d}"

# Locations
US = "Union Square"
NH = "Nob Hill"
HA = "Haight-Ashbury"
CT = "Chinatown"
MD = "Marina District"

# Travel times (minutes), directed
travel = {
    (US, NH): 9,
    (US, HA): 18,
    (US, CT): 7,
    (US, MD): 18,

    (NH, US): 7,
    (NH, HA): 13,
    (NH, CT): 6,
    (NH, MD): 11,

    (HA, US): 17,
    (HA, NH): 15,
    (HA, CT): 19,
    (HA, MD): 17,

    (CT, US): 7,
    (CT, NH): 8,
    (CT, HA): 19,
    (CT, MD): 12,

    (MD, US): 16,
    (MD, NH): 12,
    (MD, HA): 16,
    (MD, CT): 16,
}

# Friends data: location, availability start, availability end, min duration
friends = {
    "Karen":  {"loc": NH, "start": to_minutes("21:15"), "end": to_minutes("21:45"), "dur": 30},
    "Joseph": {"loc": HA, "start": to_minutes("12:30"), "end": to_minutes("19:45"), "dur": 90},
    "Sandra": {"loc": CT, "start": to_minutes("07:15"), "end": to_minutes("19:15"), "dur": 75},
    "Nancy":  {"loc": MD, "start": to_minutes("11:00"), "end": to_minutes("20:15"), "dur": 105},
}

origin_time = to_minutes("09:00")
origin_loc = US

opt = Optimize()

# Variables per friend
vars_map = {}
for name, info in friends.items():
    s = Int(f"{name}_start")
    e = Int(f"{name}_end")
    m = Bool(f"{name}_meet")
    vars_map[name] = (s, e, m)

    # Bounds on time
    opt.add(s >= 0, s <= 24*60)
    opt.add(e >= 0, e <= 24*60)

    # Duration equals min when meeting, zero otherwise
    opt.add(e - s == If(m, info["dur"], 0))

    # Availability window (only if meeting)
    opt.add(Implies(m, s >= info["start"]))
    opt.add(Implies(m, e <= info["end"]))

    # Reachability from origin if this is the first meeting
    opt.add(Implies(m, s >= origin_time + travel[(origin_loc, info["loc"])]))

# Pairwise disjunctive travel constraints
names = list(friends.keys())
for i in range(len(names)):
    for j in range(i + 1, len(names)):
        ni, nj = names[i], names[j]
        si, ei, mi = vars_map[ni]
        sj, ej, mj = vars_map[nj]
        li, lj = friends[ni]["loc"], friends[nj]["loc"]

        b_ij = Bool(f"order_{ni}_{nj}")  # True means i before j

        # If both meetings occur, enforce order with travel time
        opt.add(Implies(And(mi, mj, b_ij), sj >= ei + travel[(li, lj)]))
        opt.add(Implies(And(mi, mj, Not(b_ij)), si >= ej + travel[(lj, li)]))

# Objective: maximize number of friends met
total_met = Sum([If(vars_map[n][2], 1, 0) for n in names])
opt.maximize(total_met)

# Tie-breaker: minimize sum of start times of meetings (earlier is better)
sum_starts = Sum([If(vars_map[n][2], vars_map[n][0], 0) for n in names])
opt.minimize(sum_starts)

# Solve
if opt.check() != None:
    model = opt.model()
    itinerary = []
    for name in names:
        s, e, m = vars_map[name]
        if model[m] is not None and model[m] == True:
            itinerary.append((
                model[s].as_long(),
                {
                    "action": "meet",
                    "person": name,
                    "start_time": fmt_time(model[s].as_long()),
                    "end_time": fmt_time(model[e].as_long()),
                }
            ))
    # Sort by start time
    itinerary.sort(key=lambda x: x[0])
    itinerary = [entry for _, entry in itinerary]
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))
else:
    print(json.dumps({"itinerary": []}, ensure_ascii=False))