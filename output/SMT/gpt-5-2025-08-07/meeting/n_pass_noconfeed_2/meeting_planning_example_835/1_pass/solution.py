# SOLUTION:
import json
from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, Implies

def minutes(h, m):
    return h * 60 + m

def fmt_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times (in minutes)
T = {
    "Pacific Heights": {
        "Golden Gate Park": 15,
        "The Castro": 16,
        "Bayview": 22,
        "Marina District": 6,
        "Union Square": 12,
        "Sunset District": 21,
        "Alamo Square": 10,
        "Financial District": 13,
        "Mission District": 15
    },
    "Golden Gate Park": {
        "Pacific Heights": 16,
        "The Castro": 13,
        "Bayview": 23,
        "Marina District": 16,
        "Union Square": 22,
        "Sunset District": 10,
        "Alamo Square": 9,
        "Financial District": 26,
        "Mission District": 17
    },
    "The Castro": {
        "Pacific Heights": 16,
        "Golden Gate Park": 11,
        "Bayview": 19,
        "Marina District": 21,
        "Union Square": 19,
        "Sunset District": 17,
        "Alamo Square": 8,
        "Financial District": 21,
        "Mission District": 7
    },
    "Bayview": {
        "Pacific Heights": 23,
        "Golden Gate Park": 22,
        "The Castro": 19,
        "Marina District": 27,
        "Union Square": 18,
        "Sunset District": 23,
        "Alamo Square": 16,
        "Financial District": 19,
        "Mission District": 13
    },
    "Marina District": {
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
        "The Castro": 22,
        "Bayview": 27,
        "Union Square": 16,
        "Sunset District": 19,
        "Alamo Square": 15,
        "Financial District": 17,
        "Mission District": 20
    },
    "Union Square": {
        "Pacific Heights": 15,
        "Golden Gate Park": 22,
        "The Castro": 17,
        "Bayview": 15,
        "Marina District": 18,
        "Sunset District": 27,
        "Alamo Square": 15,
        "Financial District": 9,
        "Mission District": 14
    },
    "Sunset District": {
        "Pacific Heights": 21,
        "Golden Gate Park": 11,
        "The Castro": 17,
        "Bayview": 22,
        "Marina District": 21,
        "Union Square": 30,
        "Alamo Square": 17,
        "Financial District": 30,
        "Mission District": 25
    },
    "Alamo Square": {
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "The Castro": 8,
        "Bayview": 16,
        "Marina District": 15,
        "Union Square": 14,
        "Sunset District": 16,
        "Financial District": 17,
        "Mission District": 10
    },
    "Financial District": {
        "Pacific Heights": 13,
        "Golden Gate Park": 23,
        "The Castro": 20,
        "Bayview": 19,
        "Marina District": 15,
        "Union Square": 9,
        "Sunset District": 30,
        "Alamo Square": 17,
        "Mission District": 17
    },
    "Mission District": {
        "Pacific Heights": 16,
        "Golden Gate Park": 17,
        "The Castro": 7,
        "Bayview": 14,
        "Marina District": 19,
        "Union Square": 15,
        "Sunset District": 24,
        "Alamo Square": 11,
        "Financial District": 15
    }
}

start_location = "Pacific Heights"
start_time = minutes(9, 0)

friends = [
    {"person": "Helen",     "location": "Golden Gate Park", "avail_start": minutes(9,30),  "avail_end": minutes(12,15), "min_dur": 45},
    {"person": "Steven",    "location": "The Castro",       "avail_start": minutes(20,15), "avail_end": minutes(22,0),  "min_dur": 105},
    {"person": "Deborah",   "location": "Bayview",          "avail_start": minutes(8,30),  "avail_end": minutes(12,0),  "min_dur": 30},
    {"person": "Matthew",   "location": "Marina District",  "avail_start": minutes(9,15),  "avail_end": minutes(14,15), "min_dur": 45},
    {"person": "Joseph",    "location": "Union Square",     "avail_start": minutes(14,15), "avail_end": minutes(18,45), "min_dur": 120},
    {"person": "Ronald",    "location": "Sunset District",  "avail_start": minutes(16,0),  "avail_end": minutes(20,45), "min_dur": 60},
    {"person": "Robert",    "location": "Alamo Square",     "avail_start": minutes(18,30), "avail_end": minutes(21,15), "min_dur": 120},
    {"person": "Rebecca",   "location": "Financial District","avail_start": minutes(14,45),"avail_end": minutes(16,15), "min_dur": 30},
    {"person": "Elizabeth", "location": "Mission District", "avail_start": minutes(18,30), "avail_end": minutes(21,0),  "min_dur": 120},
]

# Initialize Z3 Optimize
opt = Optimize()

# Variables per friend
vars_map = {}
for f in friends:
    name = f["person"]
    s = Int(f"s_{name}")
    e = Int(f"e_{name}")
    d = Int(f"d_{name}")
    v = Bool(f"v_{name}")
    vars_map[name] = {"start": s, "end": e, "dur": d, "visit": v}

    # Base bounds
    opt.add(Implies(v, And(
        s >= f["avail_start"],
        e <= f["avail_end"],
        d >= f["min_dur"],
        e == s + d,
        # Must be reachable from start considering at least first leg from start_location
        s >= start_time + T[start_location][f["location"]]
    )))
    # Basic non-negativity bounds even if not visiting (loose bounds)
    opt.add(s >= 0, e >= 0, d >= 0, e == s + d)

# Pairwise ordering and travel-time feasibility
n = len(friends)
before = {}
for i in range(n):
    for j in range(i+1, n):
        fi = friends[i]["person"]
        fj = friends[j]["person"]
        loc_i = friends[i]["location"]
        loc_j = friends[j]["location"]
        s_i = vars_map[fi]["start"]
        e_i = vars_map[fi]["end"]
        v_i = vars_map[fi]["visit"]
        s_j = vars_map[fj]["start"]
        e_j = vars_map[fj]["end"]
        v_j = vars_map[fj]["visit"]
        b_ij = Bool(f"before_{fi}_then_{fj}")
        before[(fi, fj)] = b_ij

        tij = T[loc_i][loc_j]
        tji = T[loc_j][loc_i]

        # If both visited, enforce a valid order with travel time
        opt.add(Implies(And(v_i, v_j), Or(
            And(b_ij, s_j >= e_i + tij),
            And(Not(b_ij), s_i >= e_j + tji)
        )))

# Objective: maximize number of visits
visit_sum = Sum([If(vars_map[f["person"]]["visit"], 1, 0) for f in friends])
opt.maximize(visit_sum)

# Solve
if opt.check() !=  sat:
    # Should be satisfiable; fallback to empty itinerary
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()
    itinerary = []
    for f in friends:
        name = f["person"]
        v = m.eval(vars_map[name]["visit"], model_completion=True)
        if v is True:
            start = m.eval(vars_map[name]["start"]).as_long()
            end = m.eval(vars_map[name]["end"]).as_long()
            itinerary.append({
                "action": "meet",
                "location": f["location"],
                "person": name,
                "start_time": fmt_time(start),
                "end_time": fmt_time(end)
            })

    # Sort by start time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))