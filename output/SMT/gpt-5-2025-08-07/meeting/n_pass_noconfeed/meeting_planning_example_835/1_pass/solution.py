import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Locations
PH = "Pacific Heights"
GGP = "Golden Gate Park"
CASTRO = "The Castro"
BAYVIEW = "Bayview"
MARINA = "Marina District"
UNION = "Union Square"
SUNSET = "Sunset District"
ALAMO = "Alamo Square"
FIN = "Financial District"
MISSION = "Mission District"

# Travel times in minutes (directed)
travel = {
    PH: {
        GGP: 15, CASTRO: 16, BAYVIEW: 22, MARINA: 6, UNION: 12, SUNSET: 21, ALAMO: 10, FIN: 13, MISSION: 15
    },
    GGP: {
        PH: 16, CASTRO: 13, BAYVIEW: 23, MARINA: 16, UNION: 22, SUNSET: 10, ALAMO: 9, FIN: 26, MISSION: 17
    },
    CASTRO: {
        PH: 16, GGP: 11, BAYVIEW: 19, MARINA: 21, UNION: 19, SUNSET: 17, ALAMO: 8, FIN: 21, MISSION: 7
    },
    BAYVIEW: {
        PH: 23, GGP: 22, CASTRO: 19, MARINA: 27, UNION: 18, SUNSET: 23, ALAMO: 16, FIN: 19, MISSION: 13
    },
    MARINA: {
        PH: 7, GGP: 18, CASTRO: 22, BAYVIEW: 27, UNION: 16, SUNSET: 19, ALAMO: 15, FIN: 17, MISSION: 20
    },
    UNION: {
        PH: 15, GGP: 22, CASTRO: 17, BAYVIEW: 15, MARINA: 18, SUNSET: 27, ALAMO: 15, FIN: 9, MISSION: 14
    },
    SUNSET: {
        PH: 21, GGP: 11, CASTRO: 17, BAYVIEW: 22, MARINA: 21, UNION: 30, ALAMO: 17, FIN: 30, MISSION: 25
    },
    ALAMO: {
        PH: 10, GGP: 9, CASTRO: 8, BAYVIEW: 16, MARINA: 15, UNION: 14, SUNSET: 16, FIN: 17, MISSION: 10
    },
    FIN: {
        PH: 13, GGP: 23, CASTRO: 20, BAYVIEW: 19, MARINA: 15, UNION: 9, SUNSET: 30, ALAMO: 17, MISSION: 17
    },
    MISSION: {
        PH: 16, GGP: 17, CASTRO: 7, BAYVIEW: 14, MARINA: 19, UNION: 15, SUNSET: 24, ALAMO: 11, FIN: 15
    },
}

# Friends and their meeting constraints
friends = [
    {"name": "Helen", "location": GGP, "avail_start": minutes(9,30),  "avail_end": minutes(12,15), "min_duration": 45},
    {"name": "Steven", "location": CASTRO, "avail_start": minutes(20,15), "avail_end": minutes(22,0),  "min_duration": 105},
    {"name": "Deborah", "location": BAYVIEW, "avail_start": minutes(8,30),  "avail_end": minutes(12,0),  "min_duration": 30},
    {"name": "Matthew", "location": MARINA, "avail_start": minutes(9,15),  "avail_end": minutes(14,15), "min_duration": 45},
    {"name": "Joseph", "location": UNION, "avail_start": minutes(14,15), "avail_end": minutes(18,45), "min_duration": 120},
    {"name": "Ronald", "location": SUNSET, "avail_start": minutes(16,0),  "avail_end": minutes(20,45), "min_duration": 60},
    {"name": "Robert", "location": ALAMO, "avail_start": minutes(18,30), "avail_end": minutes(21,15), "min_duration": 120},
    {"name": "Rebecca", "location": FIN, "avail_start": minutes(14,45), "avail_end": minutes(16,15), "min_duration": 30},
    {"name": "Elizabeth", "location": MISSION, "avail_start": minutes(18,30), "avail_end": minutes(21,0), "min_duration": 120},
]

arrival_time = minutes(9, 0)
start_location = PH

# Z3 variables
n = len(friends)
sel = [Bool(f"sel_{i}") for i in range(n)]
start = [Int(f"start_{i}") for i in range(n)]
end = [Int(f"end_{i}") for i in range(n)]

o = Optimize()

for i, f in enumerate(friends):
    # Time domains
    o.add(start[i] >= 0, start[i] <= 24*60)
    o.add(end[i] >= 0, end[i] <= 24*60)
    o.add(end[i] >= start[i])
    # If selected, obey availability and min duration
    o.add(Implies(sel[i],
                  And(
                      start[i] >= f["avail_start"],
                      end[i] <= f["avail_end"],
                      end[i] - start[i] >= f["min_duration"],
                      # Must be reachable from arrival location at 9:00
                      start[i] >= arrival_time + travel[start_location][f["location"]]
                  )))
    # If not selected, allow degenerate times
    o.add(Implies(Not(sel[i]), And(start[i] == 0, end[i] == 0)))

# Pairwise non-overlap with travel between locations if both selected
for i in range(n):
    for j in range(i+1, n):
        li = friends[i]["location"]
        lj = friends[j]["location"]
        tij = travel[li][lj]
        tji = travel[lj][li]
        o.add(Implies(And(sel[i], sel[j]),
                      Or(end[i] + tij <= start[j],
                         end[j] + tji <= start[i])))

# Objectives: maximize number of friends met, then maximize total meeting time
total_met = Sum([If(sel[i], 1, 0) for i in range(n)])
total_minutes = Sum([If(sel[i], end[i] - start[i], 0) for i in range(n)])
o.maximize(total_met)
o.maximize(total_minutes)

if o.check() != sat:
    print(json.dumps({"itinerary": []}))
else:
    m = o.model()
    itinerary = []
    for i, f in enumerate(friends):
        if is_true(m[sel[i]]):
            s = m[start[i]].as_long()
            e = m[end[i]].as_long()
            itinerary.append({
                "action": "meet",
                "location": f["location"],
                "person": f["name"],
                "start_time": minutes_to_str(s),
                "end_time": minutes_to_str(e)
            })
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0])*60 + int(x["start_time"].split(":")[1])))
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))