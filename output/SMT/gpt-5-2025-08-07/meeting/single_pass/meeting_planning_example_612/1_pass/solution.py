# pip install z3-solver
from z3 import *
import json

# Time helpers
def to_minutes(h, m):
    return h * 60 + m

BASE = to_minutes(9, 0)  # Start day at 09:00
def minutes_since_base(h, m):
    return to_minutes(h, m) - BASE

def fmt_time_from_base(t):
    total = BASE + t
    h = total // 60
    m = total % 60
    return f"{h:02d}:{m:02d}"

# Travel times (in minutes) between neighborhoods
T = {
    "Alamo Square": {
        "Russian Hill": 13, "Presidio": 18, "Chinatown": 16,
        "Sunset District": 16, "The Castro": 8, "Embarcadero": 17,
        "Golden Gate Park": 9
    },
    "Russian Hill": {
        "Alamo Square": 15, "Presidio": 14, "Chinatown": 9,
        "Sunset District": 23, "The Castro": 21, "Embarcadero": 8,
        "Golden Gate Park": 21
    },
    "Presidio": {
        "Alamo Square": 18, "Russian Hill": 14, "Chinatown": 21,
        "Sunset District": 15, "The Castro": 21, "Embarcadero": 20,
        "Golden Gate Park": 12
    },
    "Chinatown": {
        "Alamo Square": 17, "Russian Hill": 7, "Presidio": 19,
        "Sunset District": 29, "The Castro": 22, "Embarcadero": 5,
        "Golden Gate Park": 23
    },
    "Sunset District": {
        "Alamo Square": 17, "Russian Hill": 24, "Presidio": 16,
        "Chinatown": 30, "The Castro": 17, "Embarcadero": 31,
        "Golden Gate Park": 11
    },
    "The Castro": {
        "Alamo Square": 8, "Russian Hill": 18, "Presidio": 20,
        "Chinatown": 20, "Sunset District": 17, "Embarcadero": 22,
        "Golden Gate Park": 11
    },
    "Embarcadero": {
        "Alamo Square": 19, "Russian Hill": 8, "Presidio": 20,
        "Chinatown": 7, "Sunset District": 30, "The Castro": 25,
        "Golden Gate Park": 25
    },
    "Golden Gate Park": {
        "Alamo Square": 10, "Russian Hill": 19, "Presidio": 11,
        "Chinatown": 23, "Sunset District": 10, "The Castro": 13,
        "Embarcadero": 25
    }
}

# Friends data
friends = [
    {
        "name": "Emily", "loc": "Russian Hill",
        "avail_start": minutes_since_base(12, 15),
        "avail_end": minutes_since_base(14, 15),
        "min_dur": 105
    },
    {
        "name": "Mark", "loc": "Presidio",
        "avail_start": minutes_since_base(14, 45),
        "avail_end": minutes_since_base(19, 30),
        "min_dur": 60
    },
    {
        "name": "Deborah", "loc": "Chinatown",
        "avail_start": minutes_since_base(7, 30),
        "avail_end": minutes_since_base(15, 30),
        "min_dur": 45
    },
    {
        "name": "Margaret", "loc": "Sunset District",
        "avail_start": minutes_since_base(21, 30),
        "avail_end": minutes_since_base(22, 30),
        "min_dur": 60
    },
    {
        "name": "George", "loc": "The Castro",
        "avail_start": minutes_since_base(7, 30),
        "avail_end": minutes_since_base(14, 15),
        "min_dur": 60
    },
    {
        "name": "Andrew", "loc": "Embarcadero",
        "avail_start": minutes_since_base(20, 15),
        "avail_end": minutes_since_base(22, 0),
        "min_dur": 75
    },
    {
        "name": "Steven", "loc": "Golden Gate Park",
        "avail_start": minutes_since_base(11, 15),
        "avail_end": minutes_since_base(21, 15),
        "min_dur": 105
    },
]

# Clip availability start to not before day base (09:00)
for f in friends:
    f["avail_start"] = max(0, f["avail_start"])

# Horizon: allow until 22:30 (last window end)
H = minutes_since_base(22, 30)

opt = Optimize()

# Variables
s_vars = {}
e_vars = {}
m_vars = {}

for f in friends:
    s = Int(f"s_{f['name']}")
    e = Int(f"e_{f['name']}")
    meet = Bool(f"meet_{f['name']}")
    s_vars[f['name']] = s
    e_vars[f['name']] = e
    m_vars[f['name']] = meet

    # Bounds
    opt.add(s >= 0, e >= 0, s <= H, e <= H)

    # Meeting constraints if chosen
    ai, bi, dur = f["avail_start"], f["avail_end"], f["min_dur"]
    loc = f["loc"]

    # Must have enough time within window for meeting
    opt.add(Implies(meet, And(
        s >= ai,
        e <= bi,
        e - s >= dur,
        # Cannot start before traveling from start at 09:00
        s >= T["Alamo Square"][loc]
    )))
    # If not meeting, collapse interval
    opt.add(Implies(Not(meet), And(s == 0, e == 0)))

# Non-overlap with travel times between any two meetings
for i in range(len(friends)):
    for j in range(i + 1, len(friends)):
        fi = friends[i]
        fj = friends[j]
        si, ei, mi, li = s_vars[fi["name"]], e_vars[fi["name"]], m_vars[fi["name"]], fi["loc"]
        sj, ej, mj, lj = s_vars[fj["name"]], e_vars[fj["name"]], m_vars[fj["name"]], fj["loc"]

        # If both are met, either i before j with travel or j before i with travel
        opt.add(Implies(And(mi, mj), Or(
            ei + T[li][lj] <= sj,
            ej + T[lj][li] <= si
        )))

# Objective: maximize number of friends met
opt.maximize(Sum([If(m_vars[f["name"]], 1, 0) for f in friends]))

# Secondary objective: minimize total finish time to prefer earlier schedules
opt.minimize(Sum([e_vars[f["name"]] for f in friends]))

if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
else:
    model = opt.model()
    meetings = []
    for f in friends:
        if is_true(model[m_vars[f["name"]]]):
            s = model[s_vars[f["name"]]].as_long()
            e = model[e_vars[f["name"]]].as_long()
            meetings.append({
                "person": f["name"],
                "start": s,
                "end": e
            })
    # Sort by start time
    meetings.sort(key=lambda x: x["start"])
    itinerary = []
    for m in meetings:
        itinerary.append({
            "action": "meet",
            "person": m["person"],
            "start_time": fmt_time_from_base(m["start"]),
            "end_time": fmt_time_from_base(m["end"])
        })
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))