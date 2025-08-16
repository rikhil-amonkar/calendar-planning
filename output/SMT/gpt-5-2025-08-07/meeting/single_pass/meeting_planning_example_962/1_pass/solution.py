# Requires: z3-solver (pip install z3-solver)
from z3 import *
import json

# Time helpers
def to_min(s):
    h, m = map(int, s.split(":"))
    return h * 60 + m

def fmt(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Locations
locs = [
    "The Castro",
    "Marina District",
    "Presidio",
    "North Beach",
    "Embarcadero",
    "Haight-Ashbury",
    "Golden Gate Park",
    "Richmond District",
    "Alamo Square",
    "Financial District",
    "Sunset District",
]

# Travel time matrix (directed, minutes)
T = {L: {} for L in locs}
def set_t(a,b,t): T[a][b] = t

# Fill travel times (as given)
set_t("The Castro", "Marina District", 21)
set_t("The Castro", "Presidio", 20)
set_t("The Castro", "North Beach", 20)
set_t("The Castro", "Embarcadero", 22)
set_t("The Castro", "Haight-Ashbury", 6)
set_t("The Castro", "Golden Gate Park", 11)
set_t("The Castro", "Richmond District", 16)
set_t("The Castro", "Alamo Square", 8)
set_t("The Castro", "Financial District", 21)
set_t("The Castro", "Sunset District", 17)

set_t("Marina District", "The Castro", 22)
set_t("Marina District", "Presidio", 10)
set_t("Marina District", "North Beach", 11)
set_t("Marina District", "Embarcadero", 14)
set_t("Marina District", "Haight-Ashbury", 16)
set_t("Marina District", "Golden Gate Park", 18)
set_t("Marina District", "Richmond District", 11)
set_t("Marina District", "Alamo Square", 15)
set_t("Marina District", "Financial District", 17)
set_t("Marina District", "Sunset District", 19)

set_t("Presidio", "The Castro", 21)
set_t("Presidio", "Marina District", 11)
set_t("Presidio", "North Beach", 18)
set_t("Presidio", "Embarcadero", 20)
set_t("Presidio", "Haight-Ashbury", 15)
set_t("Presidio", "Golden Gate Park", 12)
set_t("Presidio", "Richmond District", 7)
set_t("Presidio", "Alamo Square", 19)
set_t("Presidio", "Financial District", 23)
set_t("Presidio", "Sunset District", 15)

set_t("North Beach", "The Castro", 23)
set_t("North Beach", "Marina District", 9)
set_t("North Beach", "Presidio", 17)
set_t("North Beach", "Embarcadero", 6)
set_t("North Beach", "Haight-Ashbury", 18)
set_t("North Beach", "Golden Gate Park", 22)
set_t("North Beach", "Richmond District", 18)
set_t("North Beach", "Alamo Square", 16)
set_t("North Beach", "Financial District", 8)
set_t("North Beach", "Sunset District", 27)

set_t("Embarcadero", "The Castro", 25)
set_t("Embarcadero", "Marina District", 12)
set_t("Embarcadero", "Presidio", 20)
set_t("Embarcadero", "North Beach", 5)
set_t("Embarcadero", "Haight-Ashbury", 21)
set_t("Embarcadero", "Golden Gate Park", 25)
set_t("Embarcadero", "Richmond District", 21)
set_t("Embarcadero", "Alamo Square", 19)
set_t("Embarcadero", "Financial District", 5)
set_t("Embarcadero", "Sunset District", 30)

set_t("Haight-Ashbury", "The Castro", 6)
set_t("Haight-Ashbury", "Marina District", 17)
set_t("Haight-Ashbury", "Presidio", 15)
set_t("Haight-Ashbury", "North Beach", 19)
set_t("Haight-Ashbury", "Embarcadero", 20)
set_t("Haight-Ashbury", "Golden Gate Park", 7)
set_t("Haight-Ashbury", "Richmond District", 10)
set_t("Haight-Ashbury", "Alamo Square", 5)
set_t("Haight-Ashbury", "Financial District", 21)
set_t("Haight-Ashbury", "Sunset District", 15)

set_t("Golden Gate Park", "The Castro", 13)
set_t("Golden Gate Park", "Marina District", 16)
set_t("Golden Gate Park", "Presidio", 11)
set_t("Golden Gate Park", "North Beach", 23)
set_t("Golden Gate Park", "Embarcadero", 25)
set_t("Golden Gate Park", "Haight-Ashbury", 7)
set_t("Golden Gate Park", "Richmond District", 7)
set_t("Golden Gate Park", "Alamo Square", 9)
set_t("Golden Gate Park", "Financial District", 26)
set_t("Golden Gate Park", "Sunset District", 10)

set_t("Richmond District", "The Castro", 16)
set_t("Richmond District", "Marina District", 9)
set_t("Richmond District", "Presidio", 7)
set_t("Richmond District", "North Beach", 17)
set_t("Richmond District", "Embarcadero", 19)
set_t("Richmond District", "Haight-Ashbury", 10)
set_t("Richmond District", "Golden Gate Park", 9)
set_t("Richmond District", "Alamo Square", 13)
set_t("Richmond District", "Financial District", 22)
set_t("Richmond District", "Sunset District", 11)

set_t("Alamo Square", "The Castro", 8)
set_t("Alamo Square", "Marina District", 15)
set_t("Alamo Square", "Presidio", 17)
set_t("Alamo Square", "North Beach", 15)
set_t("Alamo Square", "Embarcadero", 16)
set_t("Alamo Square", "Haight-Ashbury", 5)
set_t("Alamo Square", "Golden Gate Park", 9)
set_t("Alamo Square", "Richmond District", 11)
set_t("Alamo Square", "Financial District", 17)
set_t("Alamo Square", "Sunset District", 16)

set_t("Financial District", "The Castro", 20)
set_t("Financial District", "Marina District", 15)
set_t("Financial District", "Presidio", 22)
set_t("Financial District", "North Beach", 7)
set_t("Financial District", "Embarcadero", 4)
set_t("Financial District", "Haight-Ashbury", 19)
set_t("Financial District", "Golden Gate Park", 23)
set_t("Financial District", "Richmond District", 21)
set_t("Financial District", "Alamo Square", 17)
set_t("Financial District", "Sunset District", 30)

set_t("Sunset District", "The Castro", 17)
set_t("Sunset District", "Marina District", 21)
set_t("Sunset District", "Presidio", 16)
set_t("Sunset District", "North Beach", 28)
set_t("Sunset District", "Embarcadero", 30)
set_t("Sunset District", "Haight-Ashbury", 15)
set_t("Sunset District", "Golden Gate Park", 11)
set_t("Sunset District", "Richmond District", 12)
set_t("Sunset District", "Alamo Square", 17)
set_t("Sunset District", "Financial District", 30)

# Friends with avail windows and minimum durations
friends = [
    {"name": "Elizabeth", "loc": "Marina District",   "start": to_min("19:00"), "end": to_min("20:45"), "min": 105},
    {"name": "Joshua",    "loc": "Presidio",          "start": to_min("08:30"), "end": to_min("13:15"), "min": 105},
    {"name": "Timothy",   "loc": "North Beach",       "start": to_min("19:45"), "end": to_min("22:00"), "min": 90},
    {"name": "David",     "loc": "Embarcadero",       "start": to_min("10:45"), "end": to_min("12:30"), "min": 30},
    {"name": "Kimberly",  "loc": "Haight-Ashbury",    "start": to_min("16:45"), "end": to_min("21:30"), "min": 75},
    {"name": "Lisa",      "loc": "Golden Gate Park",  "start": to_min("17:30"), "end": to_min("21:45"), "min": 45},
    {"name": "Ronald",    "loc": "Richmond District", "start": to_min("08:00"), "end": to_min("09:30"), "min": 90},
    {"name": "Stephanie", "loc": "Alamo Square",      "start": to_min("15:30"), "end": to_min("16:30"), "min": 30},
    {"name": "Helen",     "loc": "Financial District","start": to_min("17:30"), "end": to_min("18:30"), "min": 45},
    {"name": "Laura",     "loc": "Sunset District",   "start": to_min("17:45"), "end": to_min("21:15"), "min": 90},
]

start_location = "The Castro"
arrival_time = to_min("09:00")

# Z3 model
opt = Optimize()

n = len(friends)
meet = [Bool(f"meet_{i}") for i in range(n)]
svar = [Int(f"start_{i}") for i in range(n)]
evar = [Int(f"end_{i}") for i in range(n)]

for i, f in enumerate(friends):
    # Domain
    opt.add(svar[i] >= 0, svar[i] <= 24*60 + 60)  # Allow up to 25:00 just in case
    opt.add(evar[i] >= 0, evar[i] <= 24*60 + 60)
    opt.add(evar[i] >= svar[i])  # non-negative duration always

    # Availability and minimum duration if meeting
    avail_start = f["start"]
    avail_end = f["end"]
    min_dur = f["min"]
    loc = f["loc"]

    # Must be reachable after arriving at The Castro
    base_arrival = arrival_time + T[start_location][loc]

    opt.add(Implies(meet[i], svar[i] >= avail_start))
    opt.add(Implies(meet[i], evar[i] <= avail_end))
    opt.add(Implies(meet[i], evar[i] - svar[i] >= min_dur))
    opt.add(Implies(meet[i], svar[i] >= base_arrival))

# Travel feasibility and no-overlap across all met meetings
for i in range(n):
    for j in range(i+1, n):
        loc_i = friends[i]["loc"]
        loc_j = friends[j]["loc"]
        tij = T[loc_i][loc_j]
        tji = T[loc_j][loc_i]
        # If both meetings are chosen, either i finishes + travel(i->j) before j starts OR vice versa
        opt.add(Implies(And(meet[i], meet[j]),
                        Or(evar[i] + tij <= svar[j],
                           evar[j] + tji <= svar[i])))

# Objective: maximize number of friends met, then maximize total meeting time
count = Sum([If(meet[i], 1, 0) for i in range(n)])
total_duration = Sum([If(meet[i], evar[i] - svar[i], 0) for i in range(n)])
opt.maximize(count)
opt.maximize(total_duration)

# Solve
if opt.check() != sat:
    raise RuntimeError("No feasible schedule found.")
m = opt.model()

# Build itinerary
meetings = []
for i, f in enumerate(friends):
    if is_true(m.evaluate(meet[i])):
        st = int(m.evaluate(svar[i]).as_long())
        et = int(m.evaluate(evar[i]).as_long())
        meetings.append({
            "action": "meet",
            "person": f["name"],
            "start_time": fmt(st),
            "end_time": fmt(et)
        })

# Sort by start time
meetings.sort(key=lambda x: to_min(x["start_time"]))

print(json.dumps({"itinerary": meetings}, ensure_ascii=False))