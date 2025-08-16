# Solve the SF day scheduling problem using Z3 Optimize to maximize number of friends met.

from z3 import *
import json

def to_min(hhmm):
    hh, mm = map(int, hhmm.split(":"))
    return hh*60 + mm

def to_hhmm(m):
    hh = m // 60
    mm = m % 60
    return f"{hh:02d}:{mm:02d}"

# Data
start_loc = "Union Square"
start_time = to_min("09:00")

people = [
    {"name": "Betty",    "loc": "Russian Hill",   "avail_start": to_min("07:00"), "avail_end": to_min("16:45"), "dur": 105},
    {"name": "Melissa",  "loc": "Alamo Square",   "avail_start": to_min("09:30"), "avail_end": to_min("17:15"), "dur": 105},
    {"name": "Joshua",   "loc": "Haight-Ashbury", "avail_start": to_min("12:15"), "avail_end": to_min("19:00"), "dur": 90},
    {"name": "Jeffrey",  "loc": "Marina District","avail_start": to_min("12:15"), "avail_end": to_min("18:00"), "dur": 45},
    {"name": "James",    "loc": "Bayview",        "avail_start": to_min("07:30"), "avail_end": to_min("20:00"), "dur": 90},
    {"name": "Anthony",  "loc": "Chinatown",      "avail_start": to_min("11:45"), "avail_end": to_min("13:30"), "dur": 75},
    {"name": "Timothy",  "loc": "Presidio",       "avail_start": to_min("12:30"), "avail_end": to_min("14:45"), "dur": 90},
    {"name": "Emily",    "loc": "Sunset District","avail_start": to_min("19:30"), "avail_end": to_min("21:30"), "dur": 120},
]

locs = [
    "Union Square",
    "Russian Hill",
    "Alamo Square",
    "Haight-Ashbury",
    "Marina District",
    "Bayview",
    "Chinatown",
    "Presidio",
    "Sunset District",
]

# Travel times (minutes), directed
t = {L: {} for L in locs}

# Union Square to others
t["Union Square"]["Russian Hill"] = 13
t["Union Square"]["Alamo Square"] = 15
t["Union Square"]["Haight-Ashbury"] = 18
t["Union Square"]["Marina District"] = 18
t["Union Square"]["Bayview"] = 15
t["Union Square"]["Chinatown"] = 7
t["Union Square"]["Presidio"] = 24
t["Union Square"]["Sunset District"] = 27

# Russian Hill to ...
t["Russian Hill"]["Union Square"] = 10
t["Russian Hill"]["Alamo Square"] = 15
t["Russian Hill"]["Haight-Ashbury"] = 17
t["Russian Hill"]["Marina District"] = 7
t["Russian Hill"]["Bayview"] = 23
t["Russian Hill"]["Chinatown"] = 9
t["Russian Hill"]["Presidio"] = 14
t["Russian Hill"]["Sunset District"] = 23

# Alamo Square to ...
t["Alamo Square"]["Union Square"] = 14
t["Alamo Square"]["Russian Hill"] = 13
t["Alamo Square"]["Haight-Ashbury"] = 5
t["Alamo Square"]["Marina District"] = 15
t["Alamo Square"]["Bayview"] = 16
t["Alamo Square"]["Chinatown"] = 15
t["Alamo Square"]["Presidio"] = 17
t["Alamo Square"]["Sunset District"] = 16

# Haight-Ashbury to ...
t["Haight-Ashbury"]["Union Square"] = 19
t["Haight-Ashbury"]["Russian Hill"] = 17
t["Haight-Ashbury"]["Alamo Square"] = 5
t["Haight-Ashbury"]["Marina District"] = 17
t["Haight-Ashbury"]["Bayview"] = 18
t["Haight-Ashbury"]["Chinatown"] = 19
t["Haight-Ashbury"]["Presidio"] = 15
t["Haight-Ashbury"]["Sunset District"] = 15

# Marina District to ...
t["Marina District"]["Union Square"] = 16
t["Marina District"]["Russian Hill"] = 8
t["Marina District"]["Alamo Square"] = 15
t["Marina District"]["Haight-Ashbury"] = 16
t["Marina District"]["Bayview"] = 27
t["Marina District"]["Chinatown"] = 15
t["Marina District"]["Presidio"] = 10
t["Marina District"]["Sunset District"] = 19

# Bayview to ...
t["Bayview"]["Union Square"] = 18
t["Bayview"]["Russian Hill"] = 23
t["Bayview"]["Alamo Square"] = 16
t["Bayview"]["Haight-Ashbury"] = 19
t["Bayview"]["Marina District"] = 27
t["Bayview"]["Chinatown"] = 19
t["Bayview"]["Presidio"] = 32
t["Bayview"]["Sunset District"] = 23

# Chinatown to ...
t["Chinatown"]["Union Square"] = 7
t["Chinatown"]["Russian Hill"] = 7
t["Chinatown"]["Alamo Square"] = 17
t["Chinatown"]["Haight-Ashbury"] = 19
t["Chinatown"]["Marina District"] = 12
t["Chinatown"]["Bayview"] = 20
t["Chinatown"]["Presidio"] = 19
t["Chinatown"]["Sunset District"] = 29

# Presidio to ...
t["Presidio"]["Union Square"] = 22
t["Presidio"]["Russian Hill"] = 14
t["Presidio"]["Alamo Square"] = 19
t["Presidio"]["Haight-Ashbury"] = 15
t["Presidio"]["Marina District"] = 11
t["Presidio"]["Bayview"] = 31
t["Presidio"]["Chinatown"] = 21
t["Presidio"]["Sunset District"] = 15

# Sunset District to ...
t["Sunset District"]["Union Square"] = 30
t["Sunset District"]["Russian Hill"] = 24
t["Sunset District"]["Alamo Square"] = 17
t["Sunset District"]["Haight-Ashbury"] = 15
t["Sunset District"]["Marina District"] = 21
t["Sunset District"]["Bayview"] = 22
t["Sunset District"]["Chinatown"] = 30
t["Sunset District"]["Presidio"] = 16

# Build solver
opt = Optimize()

n = len(people)
b = []  # selected booleans
s = []  # start times (minutes)
e = []  # end times (minutes)

for i, p in enumerate(people):
    bi = Bool(f"sel_{i}")
    si = Int(f"start_{i}")
    ei = Int(f"end_{i}")
    b.append(bi)
    s.append(si)
    e.append(ei)

    # Bounds on time variables
    opt.add(si >= 0, si <= 24*60, ei >= 0, ei <= 24*60)

    # If selected, respect availability, duration, and initial travel from Union Square
    opt.add(Implies(bi, si >= p["avail_start"]))
    opt.add(Implies(bi, ei == si + p["dur"]))
    opt.add(Implies(bi, ei <= p["avail_end"]))
    opt.add(Implies(bi, si >= start_time + t[start_loc][p["loc"]]))

# Disjunctive no-overlap with travel time between any two selected meetings
for i in range(n):
    for j in range(i+1, n):
        li = people[i]["loc"]
        lj = people[j]["loc"]
        # If both selected, either i before j with enough travel, or j before i with enough travel
        opt.add(Implies(And(b[i], b[j]),
                        Or(s[j] >= e[i] + t[li][lj],
                           s[i] >= e[j] + t[lj][li])))

# Objective: maximize number of friends met
total_met = Sum([If(bi, 1, 0) for bi in b])
opt.maximize(total_met)

# Optional secondary: minimize last finish time to encourage earlier wraps (tie-breaker)
last_end = Int("last_end")
opt.add(last_end == If(Sum([If(bi,1,0) for bi in b]) == 0, start_time, Max([If(bi, e[i], start_time) for i, bi in enumerate(b)])))
opt.minimize(last_end)

res = opt.check()
if res != sat:
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()
    chosen = []
    for i, p in enumerate(people):
        if m.evaluate(b[i]):
            si = m.evaluate(s[i]).as_long()
            ei = m.evaluate(e[i]).as_long()
            chosen.append({
                "person": p["name"],
                "start": si,
                "end": ei
            })

    # Sort by start time
    chosen.sort(key=lambda x: x["start"])

    itinerary = []
    for c in chosen:
        entry = {
            "action": "meet",
            "person": c["person"],
            "start_time": to_hhmm(c["start"]),
            "end_time": to_hhmm(c["end"])
        }
        itinerary.append(entry)

    print(json.dumps({"itinerary": itinerary}))