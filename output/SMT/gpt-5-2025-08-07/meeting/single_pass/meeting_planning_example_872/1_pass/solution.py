# Requires: z3-solver (pip install z3-solver)
from z3 import *
import json

def t2m(s):
    h, m = map(int, s.split(":"))
    return h*60 + m

def m2t(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Travel times (minutes)
D = {
    "Presidio": {
        "Haight-Ashbury": 15, "Nob Hill": 18, "Russian Hill": 14, "North Beach": 18,
        "Chinatown": 21, "Union Square": 22, "Embarcadero": 20, "Financial District": 23, "Marina District": 11
    },
    "Haight-Ashbury": {
        "Presidio": 15, "Nob Hill": 15, "Russian Hill": 17, "North Beach": 19,
        "Chinatown": 19, "Union Square": 19, "Embarcadero": 20, "Financial District": 21, "Marina District": 17
    },
    "Nob Hill": {
        "Presidio": 17, "Haight-Ashbury": 13, "Russian Hill": 5, "North Beach": 8,
        "Chinatown": 6, "Union Square": 7, "Embarcadero": 9, "Financial District": 9, "Marina District": 11
    },
    "Russian Hill": {
        "Presidio": 14, "Haight-Ashbury": 17, "Nob Hill": 5, "North Beach": 5,
        "Chinatown": 9, "Union Square": 10, "Embarcadero": 8, "Financial District": 11, "Marina District": 7
    },
    "North Beach": {
        "Presidio": 17, "Haight-Ashbury": 18, "Nob Hill": 7, "Russian Hill": 4,
        "Chinatown": 6, "Union Square": 7, "Embarcadero": 6, "Financial District": 8, "Marina District": 9
    },
    "Chinatown": {
        "Presidio": 19, "Haight-Ashbury": 19, "Nob Hill": 9, "Russian Hill": 7,
        "North Beach": 3, "Union Square": 7, "Embarcadero": 5, "Financial District": 5, "Marina District": 12
    },
    "Union Square": {
        "Presidio": 24, "Haight-Ashbury": 18, "Nob Hill": 9, "Russian Hill": 13,
        "North Beach": 10, "Chinatown": 7, "Embarcadero": 11, "Financial District": 9, "Marina District": 18
    },
    "Embarcadero": {
        "Presidio": 20, "Haight-Ashbury": 21, "Nob Hill": 10, "Russian Hill": 8,
        "North Beach": 5, "Chinatown": 7, "Union Square": 10, "Financial District": 5, "Marina District": 12
    },
    "Financial District": {
        "Presidio": 22, "Haight-Ashbury": 19, "Nob Hill": 8, "Russian Hill": 11,
        "North Beach": 7, "Chinatown": 5, "Union Square": 9, "Embarcadero": 4, "Marina District": 15
    },
    "Marina District": {
        "Presidio": 10, "Haight-Ashbury": 16, "Nob Hill": 12, "Russian Hill": 8,
        "North Beach": 11, "Chinatown": 15, "Union Square": 16, "Embarcadero": 14, "Financial District": 17
    }
}

def travel(a, b):
    if a == b:
        return 0
    return D[a][b]

# People, locations, time windows, min durations (minutes)
people = {
    "Karen":    {"loc": "Haight-Ashbury",    "start": t2m("21:00"), "end": t2m("21:45"), "min": 45},
    "Jessica":  {"loc": "Nob Hill",          "start": t2m("13:45"), "end": t2m("21:00"), "min": 90},
    "Brian":    {"loc": "Russian Hill",      "start": t2m("15:30"), "end": t2m("21:45"), "min": 60},
    "Kenneth":  {"loc": "North Beach",       "start": t2m("09:45"), "end": t2m("21:00"), "min": 30},
    "Jason":    {"loc": "Chinatown",         "start": t2m("08:15"), "end": t2m("11:45"), "min": 75},
    "Stephanie":{"loc": "Union Square",      "start": t2m("14:45"), "end": t2m("18:45"), "min": 105},
    "Kimberly": {"loc": "Embarcadero",       "start": t2m("09:45"), "end": t2m("19:30"), "min": 75},
    "Steven":   {"loc": "Financial District","start": t2m("07:15"), "end": t2m("21:15"), "min": 60},
    "Mark":     {"loc": "Marina District",   "start": t2m("10:15"), "end": t2m("13:00"), "min": 75},
}

start_loc = "Presidio"
arrival_time = t2m("09:00")
day_end_bound = t2m("23:59")  # just a safe upper bound

# Z3 model
opt = Optimize()

start_vars = {p: Int(f"start_{p}") for p in people}
end_vars   = {p: Int(f"end_{p}")   for p in people}
meet_vars  = {p: Bool(f"meet_{p}") for p in people}

for p, info in people.items():
    s = start_vars[p]
    e = end_vars[p]
    meet = meet_vars[p]
    ws, we, md = info["start"], info["end"], info["min"]

    # Bounds
    opt.add(And(s >= 0, s <= day_end_bound))
    opt.add(And(e >= 0, e <= day_end_bound))

    # If meet, must lie within window and satisfy min duration
    opt.add(Implies(meet, And(s >= ws, e <= we, e - s >= md)))

    # If not meeting, collapse interval
    opt.add(Implies(Not(meet), e == s))

    # Must be reachable from Presidio arrival time
    opt.add(Implies(meet, s >= arrival_time + travel(start_loc, info["loc"])))

# No overlap with travel: ordering disjunctions
name_list = list(people.keys())
for i in range(len(name_list)):
    for j in range(i+1, len(name_list)):
        p = name_list[i]
        q = name_list[j]
        b = Bool(f"order_{p}_{q}")  # True => p before q
        Mp = meet_vars[p]
        Mq = meet_vars[q]
        sp, ep, sq, eq = start_vars[p], end_vars[p], start_vars[q], end_vars[q]
        lp, lq = people[p]["loc"], people[q]["loc"]
        tpq = travel(lp, lq)
        tqp = travel(lq, lp)

        # If both met and p before q: ep + tpq <= sq
        opt.add(Implies(And(Mp, Mq, b), ep + tpq <= sq))
        # If both met and q before p: eq + tqp <= sp
        opt.add(Implies(And(Mp, Mq, Not(b)), eq + tqp <= sp))

# Objectives:
# 1) Maximize number of friends met
obj_count = Sum([If(meet_vars[p], 1, 0) for p in people])

# 2) Among those, minimize total end times (encourages earlier finishes)
obj_sum_end = Sum([If(meet_vars[p], end_vars[p], 0) for p in people])

# 3) Also minimize total meeting time to keep to minimum durations
obj_sum_dur = Sum([If(meet_vars[p], end_vars[p] - start_vars[p], 0) for p in people])

h1 = opt.maximize(obj_count)
h2 = opt.minimize(obj_sum_end)
h3 = opt.minimize(obj_sum_dur)

assert opt.check() == sat
m = opt.model()

# Build itinerary
meetings = []
for p in people:
    if is_true(m[meet_vars[p]]):
        st = m[start_vars[p]].as_long()
        en = m[end_vars[p]].as_long()
        meetings.append((st, {
            "action": "meet",
            "person": p,
            "start_time": m2t(st),
            "end_time": m2t(en)
        }))

meetings.sort(key=lambda x: x[0])
itinerary = [entry for _, entry in meetings]

print(json.dumps({"itinerary": itinerary}))