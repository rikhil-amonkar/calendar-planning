from z3 import *
import json

# Minutes helper
def t(h, m): return h*60 + m

# Locations
CHINATOWN = "Chinatown"
MISSION = "Mission District"
ALAMO = "Alamo Square"
PACIFIC = "Pacific Heights"
UNION = "Union Square"
GGP = "Golden Gate Park"
SUNSET = "Sunset District"
PRESIDIO = "Presidio"

# Travel times (minutes), directional
T = {
    CHINATOWN: {
        MISSION: 18, ALAMO: 17, PACIFIC: 10, UNION: 7, GGP: 23, SUNSET: 29, PRESIDIO: 19
    },
    MISSION: {
        CHINATOWN: 16, ALAMO: 11, PACIFIC: 16, UNION: 15, GGP: 17, SUNSET: 24, PRESIDIO: 25
    },
    ALAMO: {
        CHINATOWN: 16, MISSION: 10, PACIFIC: 10, UNION: 14, GGP: 9, SUNSET: 16, PRESIDIO: 18
    },
    PACIFIC: {
        CHINATOWN: 11, MISSION: 15, ALAMO: 10, UNION: 12, GGP: 15, SUNSET: 21, PRESIDIO: 11
    },
    UNION: {
        CHINATOWN: 7, MISSION: 14, ALAMO: 15, PACIFIC: 15, GGP: 22, SUNSET: 26, PRESIDIO: 24
    },
    GGP: {
        CHINATOWN: 23, MISSION: 17, ALAMO: 10, PACIFIC: 16, UNION: 22, SUNSET: 10, PRESIDIO: 11
    },
    SUNSET: {
        CHINATOWN: 30, MISSION: 24, ALAMO: 17, PACIFIC: 21, UNION: 30, GGP: 11, PRESIDIO: 16
    },
    PRESIDIO: {
        CHINATOWN: 21, MISSION: 26, ALAMO: 18, PACIFIC: 11, UNION: 22, GGP: 12, SUNSET: 15
    }
}
# Add zero travel to self
for a in [CHINATOWN, MISSION, ALAMO, PACIFIC, UNION, GGP, SUNSET, PRESIDIO]:
    T.setdefault(a, {})
    T[a][a] = 0

# People with availability and minimum meeting duration
people = [
    {"name": "David",   "loc": MISSION,   "avail": (t(8,0),  t(19,45)), "min_dur": 45},
    {"name": "Kenneth", "loc": ALAMO,     "avail": (t(14,0), t(19,45)), "min_dur": 120},
    {"name": "John",    "loc": PACIFIC,   "avail": (t(17,0), t(20,0)),  "min_dur": 15},
    {"name": "Charles", "loc": UNION,     "avail": (t(21,45),t(22,45)), "min_dur": 60},
    {"name": "Deborah", "loc": GGP,       "avail": (t(7,0),  t(18,15)), "min_dur": 90},
    {"name": "Karen",   "loc": SUNSET,    "avail": (t(17,45),t(21,15)), "min_dur": 15},
    {"name": "Carol",   "loc": PRESIDIO,  "avail": (t(8,15), t(9,15)),  "min_dur": 30},
]

# Add a fixed "Start" event at Chinatown at 09:00
start_event = {"name": "__START__", "loc": CHINATOWN, "avail": (t(9,0), t(9,0)), "min_dur": 0}
events = [start_event] + people  # index 0 is Start

n = len(events)

# Z3 variables
start_vars = [Int(f"start_{i}") for i in range(n)]
end_vars   = [Int(f"end_{i}")   for i in range(n)]
sel_vars   = [Bool(f"sel_{i}")  for i in range(n)]  # we'll force sel_0 = True

# Ordering variables for pairs i<j: o_ij means i before j
order_vars = {}
for i in range(n):
    for j in range(i+1, n):
        order_vars[(i,j)] = Bool(f"o_{i}_{j}")

opt = Optimize()
M = 10000  # big M

# Constraints per event
for i, ev in enumerate(events):
    w0, w1 = ev["avail"]
    mind = ev["min_dur"]

    # Bounds
    opt.add(start_vars[i] >= 0, end_vars[i] >= 0, end_vars[i] <= t(23,59))

    if i == 0:
        # Start fixed
        opt.add(sel_vars[i] == True)
        opt.add(start_vars[i] == w0, end_vars[i] == w1)
    else:
        # If selected, obey window and duration; otherwise collapse to 0
        opt.add(Implies(sel_vars[i], And(start_vars[i] >= w0,
                                         end_vars[i]   <= w1,
                                         end_vars[i] - start_vars[i] >= mind,
                                         start_vars[i] < end_vars[i])))
        opt.add(Implies(Not(sel_vars[i]), And(start_vars[i] == 0, end_vars[i] == 0)))

# Pairwise ordering and travel feasibility
def travel(a, b):
    return T[a][b]

for i in range(n):
    for j in range(i+1, n):
        oij = order_vars[(i,j)]
        li, lj = events[i]["loc"], events[j]["loc"]
        si, sj = sel_vars[i], sel_vars[j]
        # Both selected => impose one-or-the-other ordering with travel time
        both = And(si, sj)
        # i before j case active when oij is True
        opt.add(Implies(both, end_vars[i] + travel(li, lj) <= start_vars[j] + If(oij, 0, M)))
        # j before i case active when oij is False
        opt.add(Implies(both, end_vars[j] + travel(lj, li) <= start_vars[i] + If(oij, M, 0)))

# Force Start to be before any selected person
for j in range(1, n):
    o_sj = order_vars[(0, j)]  # since 0<j
    opt.add(Implies(sel_vars[j], o_sj))

# Objective: maximize number of friends met
meet_count = Sum([If(sel_vars[i], 1, 0) for i in range(1, n)])
opt.maximize(meet_count)

# Optional tie-breakers could be added, but not necessary for max count.

if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()
    # Build itinerary of selected real meetings (exclude Start)
    meetings = []
    for i in range(1, n):
        if is_true(m[sel_vars[i]]):
            s = m[start_vars[i]].as_long()
            e = m[end_vars[i]].as_long()
            person = events[i]["name"]
            meetings.append((s, e, person))
    meetings.sort(key=lambda x: x[0])

    def fmt(mm):
        h = mm // 60
        m_ = mm % 60
        return f"{h:02d}:{m_:02d}"

    itinerary = []
    for s, e, person in meetings:
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": fmt(s),
            "end_time": fmt(e)
        })

    print(json.dumps({"itinerary": itinerary}))