# Solve the SF friend-meeting problem via Z3 Optimize to maximize the number of friends met.
# The program outputs a JSON itinerary.

from z3 import Optimize, Int, Bool, If, And, Or, Not, Xor, Implies, Sum
import json

# Helper to convert minutes to HH:MM
def to_hhmm(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

# Constants
PRESIDIO = "Presidio"
start_time_day = 9 * 60  # 09:00 -> 540

# Locations
locations = [
    "Presidio",
    "Fisherman's Wharf",
    "Alamo Square",
    "Financial District",
    "Union Square",
    "Sunset District",
    "Embarcadero",
    "Golden Gate Park",
    "Chinatown",
    "Richmond District",
]

# Travel times (directed, minutes)
t = {}
def add(a, b, m):
    t[(a, b)] = m

# Presidio
add("Presidio", "Fisherman's Wharf", 19)
add("Presidio", "Alamo Square", 19)
add("Presidio", "Financial District", 23)
add("Presidio", "Union Square", 22)
add("Presidio", "Sunset District", 15)
add("Presidio", "Embarcadero", 20)
add("Presidio", "Golden Gate Park", 12)
add("Presidio", "Chinatown", 21)
add("Presidio", "Richmond District", 7)

# Fisherman's Wharf
add("Fisherman's Wharf", "Presidio", 17)
add("Fisherman's Wharf", "Alamo Square", 21)
add("Fisherman's Wharf", "Financial District", 11)
add("Fisherman's Wharf", "Union Square", 13)
add("Fisherman's Wharf", "Sunset District", 27)
add("Fisherman's Wharf", "Embarcadero", 8)
add("Fisherman's Wharf", "Golden Gate Park", 25)
add("Fisherman's Wharf", "Chinatown", 12)
add("Fisherman's Wharf", "Richmond District", 18)

# Alamo Square
add("Alamo Square", "Presidio", 17)
add("Alamo Square", "Fisherman's Wharf", 19)
add("Alamo Square", "Financial District", 17)
add("Alamo Square", "Union Square", 14)
add("Alamo Square", "Sunset District", 16)
add("Alamo Square", "Embarcadero", 16)
add("Alamo Square", "Golden Gate Park", 9)
add("Alamo Square", "Chinatown", 15)
add("Alamo Square", "Richmond District", 11)

# Financial District
add("Financial District", "Presidio", 22)
add("Financial District", "Fisherman's Wharf", 10)
add("Financial District", "Alamo Square", 17)
add("Financial District", "Union Square", 9)
add("Financial District", "Sunset District", 30)
add("Financial District", "Embarcadero", 4)
add("Financial District", "Golden Gate Park", 23)
add("Financial District", "Chinatown", 5)
add("Financial District", "Richmond District", 21)

# Union Square
add("Union Square", "Presidio", 24)
add("Union Square", "Fisherman's Wharf", 15)
add("Union Square", "Alamo Square", 15)
add("Union Square", "Financial District", 9)
add("Union Square", "Sunset District", 27)
add("Union Square", "Embarcadero", 11)
add("Union Square", "Golden Gate Park", 22)
add("Union Square", "Chinatown", 7)
add("Union Square", "Richmond District", 20)

# Sunset District
add("Sunset District", "Presidio", 16)
add("Sunset District", "Fisherman's Wharf", 29)
add("Sunset District", "Alamo Square", 17)
add("Sunset District", "Financial District", 30)
add("Sunset District", "Union Square", 30)
add("Sunset District", "Embarcadero", 30)
add("Sunset District", "Golden Gate Park", 11)
add("Sunset District", "Chinatown", 30)
add("Sunset District", "Richmond District", 12)

# Embarcadero
add("Embarcadero", "Presidio", 20)
add("Embarcadero", "Fisherman's Wharf", 6)
add("Embarcadero", "Alamo Square", 19)
add("Embarcadero", "Financial District", 5)
add("Embarcadero", "Union Square", 10)
add("Embarcadero", "Sunset District", 30)
add("Embarcadero", "Golden Gate Park", 25)
add("Embarcadero", "Chinatown", 7)
add("Embarcadero", "Richmond District", 21)

# Golden Gate Park
add("Golden Gate Park", "Presidio", 11)
add("Golden Gate Park", "Fisherman's Wharf", 24)
add("Golden Gate Park", "Alamo Square", 9)
add("Golden Gate Park", "Financial District", 26)
add("Golden Gate Park", "Union Square", 22)
add("Golden Gate Park", "Sunset District", 10)
add("Golden Gate Park", "Embarcadero", 25)
add("Golden Gate Park", "Chinatown", 23)
add("Golden Gate Park", "Richmond District", 7)

# Chinatown
add("Chinatown", "Presidio", 19)
add("Chinatown", "Fisherman's Wharf", 8)
add("Chinatown", "Alamo Square", 17)
add("Chinatown", "Financial District", 5)
add("Chinatown", "Union Square", 7)
add("Chinatown", "Sunset District", 29)
add("Chinatown", "Embarcadero", 5)
add("Chinatown", "Golden Gate Park", 23)
add("Chinatown", "Richmond District", 20)

# Richmond District
add("Richmond District", "Presidio", 7)
add("Richmond District", "Fisherman's Wharf", 18)
add("Richmond District", "Alamo Square", 13)
add("Richmond District", "Financial District", 22)
add("Richmond District", "Union Square", 21)
add("Richmond District", "Sunset District", 11)
add("Richmond District", "Embarcadero", 19)
add("Richmond District", "Golden Gate Park", 9)
add("Richmond District", "Chinatown", 20)

# Friends data: name, location, availability start, availability end, min duration
friends = [
    ("Jeffrey",   "Fisherman's Wharf", 10*60+15, 13*60+0, 90),
    ("Ronald",    "Alamo Square",       7*60+45, 14*60+45, 120),
    ("Jason",     "Financial District", 10*60+45, 16*60+0, 105),
    ("Melissa",   "Union Square",       17*60+45, 18*60+15, 15),
    ("Elizabeth", "Sunset District",    14*60+45, 17*60+30, 105),
    ("Margaret",  "Embarcadero",        13*60+15, 19*60+0, 90),
    ("George",    "Golden Gate Park",   19*60+0, 22*60+0, 75),
    ("Richard",   "Chinatown",          9*60+30, 21*60+0, 15),
    ("Laura",     "Richmond District",  9*60+45, 18*60+0, 60),
]

names = [f[0] for f in friends]
loc_of = {f[0]: f[1] for f in friends}
avail_start = {f[0]: f[2] for f in friends}
avail_end = {f[0]: f[3] for f in friends}
min_dur = {f[0]: f[4] for f in friends}

# Z3 variables
s = {p: Int(f"s_{p}") for p in names}
e = {p: Int(f"e_{p}") for p in names}
sel = {p: Bool(f"sel_{p}") for p in names}
before = {(p,q): Bool(f"before_{p}_{q}") for p in names for q in names if p != q}

opt = Optimize()

# Basic time bounds and meeting constraints
for p in names:
    # bounds
    opt.add(s[p] >= 0, e[p] >= 0, s[p] <= 24*60, e[p] <= 24*60)
    # if selected: within availability and min duration; else degenerate
    opt.add(Implies(sel[p],
                    And(s[p] >= avail_start[p],
                        e[p] <= avail_end[p],
                        e[p] - s[p] >= min_dur[p])))
    opt.add(Implies(Not(sel[p]), And(e[p] == s[p], s[p] == avail_start[p])))

# Ordering and travel-time feasibility between any two selected meetings
for p in names:
    for q in names:
        if p == q:
            continue
        # If both selected, exactly one is before the other
        opt.add(Implies(And(sel[p], sel[q]), Xor(before[(p,q)], before[(q,p)])))
        # Enforce travel-time gap according to chosen order
        loc_p = loc_of[p]
        loc_q = loc_of[q]
        travel_pq = t[(loc_p, loc_q)]
        travel_qp = t[(loc_q, loc_p)]
        opt.add(Implies(And(sel[p], sel[q], before[(p,q)]), s[q] >= e[p] + travel_pq))
        opt.add(Implies(And(sel[p], sel[q], before[(q,p)]), s[p] >= e[q] + travel_qp))

# Anchor to starting point (Presidio at 09:00):
# For each selected meeting p, either it has a selected predecessor or it must start after 09:00 plus travel from Presidio.
for p in names:
    preds = []
    for q in names:
        if p == q: continue
        preds.append(And(sel[q], before[(q,p)]))
    must_start_after_base = (s[p] >= start_time_day + t[(PRESIDIO, loc_of[p])])
    opt.add(Implies(sel[p], Or(must_start_after_base, Or(preds))))

# Objective: maximize count of selected meetings, then minimize total end times and start times to break ties toward earlier schedules.
total_meetings = Sum([If(sel[p], 1, 0) for p in names])
opt.maximize(total_meetings)
opt.minimize(Sum([If(sel[p], e[p], 0) for p in names]))
opt.minimize(Sum([If(sel[p], s[p], 0) for p in names]))

# Solve
if opt.check() != None:
    m = opt.model()
    meetings = []
    for p in names:
        if m.eval(sel[p], model_completion=True):
            start = m.eval(s[p]).as_long()
            end = m.eval(e[p]).as_long()
            meetings.append((start, end, p))
    # Sort by start time for an itinerary
    meetings.sort(key=lambda x: x[0])
    itinerary = []
    for start, end, p in meetings:
        itinerary.append({
            "action": "meet",
            "person": p,
            "start_time": to_hhmm(start),
            "end_time": to_hhmm(end)
        })
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}))
else:
    print("SOLUTION:")
    print(json.dumps({"itinerary": []}))