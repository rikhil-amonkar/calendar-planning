# Solve the SF day scheduling problem with Z3
# Objective: maximize number of friends met subject to availability, minimum meeting durations, and travel times.
from z3 import Optimize, Int, Bool, Implies, And, Or, Xor, If, Sum, sat
import json

# Time helpers
def to_min(tstr):
    h, m = map(int, tstr.split(":"))
    return h * 60 + m

def mm_to_hhmm(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Data
start_location = "Bayview"
start_time = to_min("09:00")

friends = [
    {
        "name": "Mary",
        "location": "Pacific Heights",
        "avail_start": to_min("10:00"),
        "avail_end": to_min("19:00"),
        "min_duration": 45
    },
    {
        "name": "Lisa",
        "location": "Mission District",
        "avail_start": to_min("20:30"),
        "avail_end": to_min("22:00"),
        "min_duration": 75
    },
    {
        "name": "Betty",
        "location": "Haight-Ashbury",
        "avail_start": to_min("07:15"),
        "avail_end": to_min("17:15"),
        "min_duration": 90
    },
    {
        "name": "Charles",
        "location": "Financial District",
        "avail_start": to_min("11:15"),
        "avail_end": to_min("15:00"),
        "min_duration": 120
    }
]

# Directed travel times (in minutes)
travel = {}
def set_trv(a,b,t):
    travel[(a,b)] = t

# Bayview to others
set_trv("Bayview","Pacific Heights",23)
set_trv("Bayview","Mission District",13)
set_trv("Bayview","Haight-Ashbury",19)
set_trv("Bayview","Financial District",19)

# Others to Bayview
set_trv("Pacific Heights","Bayview",22)
set_trv("Mission District","Bayview",15)
set_trv("Haight-Ashbury","Bayview",18)
set_trv("Financial District","Bayview",19)

# Pairwise
set_trv("Pacific Heights","Mission District",15)
set_trv("Pacific Heights","Haight-Ashbury",11)
set_trv("Pacific Heights","Financial District",13)

set_trv("Mission District","Pacific Heights",16)
set_trv("Mission District","Haight-Ashbury",12)
set_trv("Mission District","Financial District",17)

set_trv("Haight-Ashbury","Pacific Heights",12)
set_trv("Haight-Ashbury","Mission District",11)
set_trv("Haight-Ashbury","Financial District",21)

set_trv("Financial District","Pacific Heights",13)
set_trv("Financial District","Mission District",17)
set_trv("Financial District","Haight-Ashbury",19)

# same-to-same
for loc in ["Bayview","Pacific Heights","Mission District","Haight-Ashbury","Financial District"]:
    set_trv(loc, loc, 0)

# Z3 model
opt = Optimize()

# Variables per friend
vars_by_name = {}
for f in friends:
    nm = f["name"]
    s = Int(f"{nm}_start")
    e = Int(f"{nm}_end")
    meet = Bool(f"{nm}_meet")
    vars_by_name[nm] = {"start": s, "end": e, "meet": meet, "info": f}

    # Domains
    opt.add(s >= 0, s <= 24*60, e >= 0, e <= 24*60)

    # If meeting, respect availability, min duration, and reachability from start
    opt.add(Implies(meet, s >= f["avail_start"]))
    opt.add(Implies(meet, e <= f["avail_end"]))
    opt.add(Implies(meet, e == s + f["min_duration"]))
    # Must be reachable from start location if meeting
    opt.add(Implies(meet, s >= start_time + travel[(start_location, f["location"])]))

    # If not meeting, collapse to 0 to avoid arbitrary values
    opt.add(Implies(~meet, And(s == 0, e == 0)))

# Pairwise ordering and travel-time feasibility
names = [f["name"] for f in friends]
before = {}  # (i,j) -> Bool means i before j
for i in range(len(names)):
    for j in range(i+1, len(names)):
        ni, nj = names[i], names[j]
        bi = Bool(f"before_{ni}_{nj}")
        bj = Bool(f"before_{nj}_{ni}")
        before[(ni, nj)] = bi
        before[(nj, ni)] = bj

        mi = vars_by_name[ni]["meet"]
        mj = vars_by_name[nj]["meet"]
        si = vars_by_name[ni]["start"]
        sj = vars_by_name[nj]["start"]
        ei = vars_by_name[ni]["end"]
        ej = vars_by_name[nj]["end"]
        li = vars_by_name[ni]["info"]["location"]
        lj = vars_by_name[nj]["info"]["location"]

        # "before" implies both meetings happen
        opt.add(Implies(bi, And(mi, mj)))
        opt.add(Implies(bj, And(mi, mj)))

        # If both meetings happen, exactly one ordering must hold
        opt.add(Implies(And(mi, mj), Xor(bi, bj)))
        # If one or both don't happen, no ordering needed (both false acceptable)
        opt.add(Implies(~And(mi, mj), And(~bi, ~bj)))

        # Travel feasibility
        opt.add(Implies(bi, sj >= ei + travel[(li, lj)]))
        opt.add(Implies(bj, si >= ej + travel[(lj, li)]))

# Objective: maximize number of meetings
count_meet = Sum([If(vars_by_name[n]["meet"], 1, 0) for n in names])
opt.maximize(count_meet)

# Optional tie-breaker: minimize sum of waiting between consecutive meetings by minimizing
# the sum of start times (a weak proxy) to avoid excessively early starts; this nudges the
# solver toward tighter schedules when ties exist.
opt.minimize(Sum([vars_by_name[n]["start"] for n in names]))

res = opt.check()
if res != sat:
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()

    # Gather meetings that are scheduled
    scheduled = []
    for n in names:
        if m.eval(vars_by_name[n]["meet"], model_completion=True):
            s = m.eval(vars_by_name[n]["start"]).as_long()
            e = m.eval(vars_by_name[n]["end"]).as_long()
            scheduled.append({
                "action": "meet",
                "person": n,
                "start_time": mm_to_hhmm(s),
                "end_time": mm_to_hhmm(e)
            })

    # Sort by start_time
    scheduled.sort(key=lambda x: to_min(x["start_time"]))

    print(json.dumps({"itinerary": scheduled}))