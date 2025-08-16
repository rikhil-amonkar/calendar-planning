# Requires: pip install z3-solver
from z3 import *
import json

def t2m(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def m2t(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Locations
locs = [
    "Marina District", "Bayview", "Sunset District", "Richmond District",
    "Nob Hill", "Chinatown", "Haight-Ashbury", "North Beach",
    "Russian Hill", "Embarcadero"
]

# Directed travel times (minutes)
D = {
    ("Marina District","Bayview"):27, ("Marina District","Sunset District"):19, ("Marina District","Richmond District"):11,
    ("Marina District","Nob Hill"):12, ("Marina District","Chinatown"):15, ("Marina District","Haight-Ashbury"):16,
    ("Marina District","North Beach"):11, ("Marina District","Russian Hill"):8, ("Marina District","Embarcadero"):14,

    ("Bayview","Marina District"):27, ("Bayview","Sunset District"):23, ("Bayview","Richmond District"):25,
    ("Bayview","Nob Hill"):20, ("Bayview","Chinatown"):19, ("Bayview","Haight-Ashbury"):19,
    ("Bayview","North Beach"):22, ("Bayview","Russian Hill"):23, ("Bayview","Embarcadero"):19,

    ("Sunset District","Marina District"):21, ("Sunset District","Bayview"):22, ("Sunset District","Richmond District"):12,
    ("Sunset District","Nob Hill"):27, ("Sunset District","Chinatown"):30, ("Sunset District","Haight-Ashbury"):15,
    ("Sunset District","North Beach"):28, ("Sunset District","Russian Hill"):24, ("Sunset District","Embarcadero"):30,

    ("Richmond District","Marina District"):9, ("Richmond District","Bayview"):27, ("Richmond District","Sunset District"):11,
    ("Richmond District","Nob Hill"):14, ("Richmond District","Chinatown"):20, ("Richmond District","Haight-Ashbury"):10,
    ("Richmond District","North Beach"):17, ("Richmond District","Russian Hill"):13, ("Richmond District","Embarcadero"):19,

    ("Nob Hill","Marina District"):11, ("Nob Hill","Bayview"):19, ("Nob Hill","Sunset District"):24,
    ("Nob Hill","Richmond District"):14, ("Nob Hill","Chinatown"):6, ("Nob Hill","Haight-Ashbury"):13,
    ("Nob Hill","North Beach"):8, ("Nob Hill","Russian Hill"):5, ("Nob Hill","Embarcadero"):9,

    ("Chinatown","Marina District"):12, ("Chinatown","Bayview"):20, ("Chinatown","Sunset District"):29,
    ("Chinatown","Richmond District"):20, ("Chinatown","Nob Hill"):9, ("Chinatown","Haight-Ashbury"):19,
    ("Chinatown","North Beach"):3, ("Chinatown","Russian Hill"):7, ("Chinatown","Embarcadero"):5,

    ("Haight-Ashbury","Marina District"):17, ("Haight-Ashbury","Bayview"):18, ("Haight-Ashbury","Sunset District"):15,
    ("Haight-Ashbury","Richmond District"):10, ("Haight-Ashbury","Nob Hill"):15, ("Haight-Ashbury","Chinatown"):19,
    ("Haight-Ashbury","North Beach"):19, ("Haight-Ashbury","Russian Hill"):17, ("Haight-Ashbury","Embarcadero"):20,

    ("North Beach","Marina District"):9, ("North Beach","Bayview"):25, ("North Beach","Sunset District"):27,
    ("North Beach","Richmond District"):18, ("North Beach","Nob Hill"):7, ("North Beach","Chinatown"):6,
    ("North Beach","Haight-Ashbury"):18, ("North Beach","Russian Hill"):4, ("North Beach","Embarcadero"):6,

    ("Russian Hill","Marina District"):7, ("Russian Hill","Bayview"):23, ("Russian Hill","Sunset District"):23,
    ("Russian Hill","Richmond District"):14, ("Russian Hill","Nob Hill"):5, ("Russian Hill","Chinatown"):9,
    ("Russian Hill","Haight-Ashbury"):17, ("Russian Hill","North Beach"):5, ("Russian Hill","Embarcadero"):8,

    ("Embarcadero","Marina District"):12, ("Embarcadero","Bayview"):21, ("Embarcadero","Sunset District"):30,
    ("Embarcadero","Richmond District"):21, ("Embarcadero","Nob Hill"):10, ("Embarcadero","Chinatown"):7,
    ("Embarcadero","Haight-Ashbury"):21, ("Embarcadero","North Beach"):5, ("Embarcadero","Russian Hill"):8,
}

# People data: name, location, window start, window end, min duration
people = [
    ("Charles",  "Bayview",          t2m("11:30"), t2m("14:30"), 45),
    ("Robert",   "Sunset District",  t2m("16:45"), t2m("21:00"), 30),
    ("Karen",    "Richmond District",t2m("19:15"), t2m("21:30"), 60),
    ("Rebecca",  "Nob Hill",         t2m("16:15"), t2m("20:30"), 90),
    ("Margaret", "Chinatown",        t2m("14:15"), t2m("19:45"), 120),
    ("Patricia", "Haight-Ashbury",   t2m("14:30"), t2m("20:30"), 45),
    ("Mark",     "North Beach",      t2m("14:00"), t2m("18:30"), 105),
    ("Melissa",  "Russian Hill",     t2m("13:00"), t2m("19:45"), 30),
    ("Laura",    "Embarcadero",      t2m("07:45"), t2m("13:15"), 105),
]

arrive_start_loc = "Marina District"
arrive_time = t2m("09:00")

# Z3 model
opt = Optimize()
sel = {}
s = {}
e = {}
for name, loc, ws, we, mind in people:
    sel[name] = Bool(f"sel_{name}")
    s[name] = Int(f"s_{name}")
    e[name] = Int(f"e_{name}")
    # Domain
    opt.add(s[name] >= 0, e[name] >= 0)
    # Time window and min duration if selected
    opt.add(Implies(sel[name], And(s[name] >= ws, e[name] <= we, e[name] - s[name] >= mind)))
    # Cannot start before earliest possible arrival from Marina at 09:00
    earliest_direct = arrive_time + D[(arrive_start_loc, loc)]
    opt.add(Implies(sel[name], s[name] >= earliest_direct))
    # If not selected, collapse times (optional tidy)
    opt.add(Implies(Not(sel[name]), e[name] == s[name]))

# Pairwise disjunctive sequencing with travel times
order = {}
for i in range(len(people)):
    ni, loci, _, _, _ = people[i]
    for j in range(i+1, len(people)):
        nj, locj, _, _, _ = people[j]
        oij = Bool(f"order_{ni}_before_{nj}")
        oji = Bool(f"order_{nj}_before_{ni}")
        order[(ni,nj)] = oij
        order[(nj,ni)] = oji
        both = And(sel[ni], sel[nj])
        # Exactly one order if both selected
        opt.add(Implies(both, Xor(oij, oji)))
        # If not both selected, no ordering is required (can be both False)
        # Timing constraints
        opt.add(Implies(And(both, oij), s[nj] >= e[ni] + D[(loci, locj)]))
        opt.add(Implies(And(both, oji), s[ni] >= e[nj] + D[(locj, loci)]))

# Objective: maximize number of meetings
total_meet = Sum([If(sel[name], 1, 0) for name, *_ in people])
opt.maximize(total_meet)

# (Optional) secondary: minimize day end time to encourage earlier finish
day_end = Int("day_end")
opt.add(day_end >= arrive_time)
for name, *_ in people:
    opt.add(day_end >= e[name])
opt.minimize(day_end)

# Solve
res = opt.check()
if res != sat:
    print(json.dumps({"itinerary": []}))
    raise SystemExit()

m = opt.model()

# Collect selected meetings
meetings = []
for name, loc, ws, we, mind in people:
    if is_true(m[sel[name]]):
        si = m[s[name]].as_long()
        ei = m[e[name]].as_long()
        meetings.append((si, {"action": "meet", "person": name, "start_time": m2t(si), "end_time": m2t(ei)}))

# Sort by start time
meetings.sort(key=lambda x: x[0])
itinerary = [entry for _, entry in meetings]

print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, separators=(",", ":")))