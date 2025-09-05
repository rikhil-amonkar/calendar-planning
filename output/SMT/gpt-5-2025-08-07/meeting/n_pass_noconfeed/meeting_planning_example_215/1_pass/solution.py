# SOLUTION:
import json
from z3 import *

def time_to_min(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Locations
BAYVIEW = "Bayview"
EMB = "Embarcadero"
RD = "Richmond District"
FW = "Fisherman's Wharf"

# Travel times (minutes), directional
travel_times = {
    (BAYVIEW, EMB): 19,
    (BAYVIEW, RD): 25,
    (BAYVIEW, FW): 25,
    (EMB, BAYVIEW): 21,
    (EMB, RD): 21,
    (EMB, FW): 6,
    (RD, BAYVIEW): 26,
    (RD, EMB): 19,
    (RD, FW): 18,
    (FW, BAYVIEW): 26,
    (FW, EMB): 8,
    (FW, RD): 18,
}

def travel(a, b):
    return travel_times[(a, b)]

# Start info
start_location = BAYVIEW
start_time = time_to_min("9:00")

# People constraints
people = {
    "Jessica": {
        "location": EMB,
        "avail_start": time_to_min("16:45"),
        "avail_end": time_to_min("19:00"),
        "min_meet": 30
    },
    "Sandra": {
        "location": RD,
        "avail_start": time_to_min("18:30"),
        "avail_end": time_to_min("21:45"),
        "min_meet": 120
    },
    "Jason": {
        "location": FW,
        "avail_start": time_to_min("16:00"),
        "avail_end": time_to_min("16:45"),
        "min_meet": 30
    }
}

# Z3 setup
opt = Optimize()
opt.set(priority='lex')

minutes_in_day = 24 * 60

vars_by_person = {}
meet_bools = []
durations = []

for name, info in people.items():
    s = Int(f"{name}_start")
    e = Int(f"{name}_end")
    meet = Bool(f"{name}_meet")
    dur = Int(f"{name}_dur")
    vars_by_person[name] = {"start": s, "end": e, "meet": meet, "dur": dur, "loc": info["location"]}

    # Bounds
    opt.add(s >= 0, s <= minutes_in_day)
    opt.add(e >= 0, e <= minutes_in_day)
    # Duration definition
    opt.add(dur == If(meet, e - s, 0))

    # Meeting window and duration constraints when meeting
    opt.add(Implies(meet, And(
        s >= info["avail_start"],
        e <= info["avail_end"],
        e > s,
        e - s >= info["min_meet"],
        # Reachable from the starting point if this were the first meeting
        s >= start_time + travel(start_location, info["location"])
    )))

    meet_bools.append(meet)
    durations.append(dur)

# Pairwise travel feasibility: if both meetings happen, they must be ordered with enough travel time
names = list(people.keys())
for i in range(len(names)):
    for j in range(i + 1, len(names)):
        ni, nj = names[i], names[j]
        vi, vj = vars_by_person[ni], vars_by_person[nj]
        li, lj = vi["loc"], vj["loc"]
        ei, sj = vi["end"], vj["start"]
        ej, si = vj["end"], vi["start"]
        ti_to_j = travel(li, lj)
        tj_to_i = travel(lj, li)
        opt.add(Implies(And(vi["meet"], vj["meet"]),
                        Or(ei + ti_to_j <= sj, ej + tj_to_i <= si)))

# Objectives: maximize number of friends met, then maximize total meeting time
meet_count = Sum([If(m, 1, 0) for m in meet_bools])
total_meeting_time = Sum(durations)

opt.maximize(meet_count)
opt.maximize(total_meeting_time)

if opt.check() != sat:
    # Fallback: no schedule found (shouldn't happen with given constraints)
    result = {"itinerary": []}
    print(json.dumps(result))
else:
    model = opt.model()
    meetings = []
    for name in names:
        v = vars_by_person[name]
        if is_true(model[v["meet"]]):
            s = model[v["start"]].as_long()
            e = model[v["end"]].as_long()
            meetings.append({
                "action": "meet",
                "location": v["loc"],
                "person": name,
                "start_time": min_to_time(s),
                "end_time": min_to_time(e)
            })

    # Sort by start time
    meetings.sort(key=lambda x: time_to_min(x["start_time"]))

    result = {"itinerary": meetings}
    print(json.dumps(result))