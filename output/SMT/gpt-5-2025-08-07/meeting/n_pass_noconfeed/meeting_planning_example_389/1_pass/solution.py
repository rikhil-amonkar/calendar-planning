# SOLUTION:
import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Locations
HA = "Haight-Ashbury"
FW = "Fisherman's Wharf"
RD = "Richmond District"
MD = "Mission District"
BV = "Bayview"

# Travel times (minutes)
dist = {
    (HA, FW): 23, (HA, RD): 10, (HA, MD): 11, (HA, BV): 18,
    (FW, HA): 22, (FW, RD): 18, (FW, MD): 22, (FW, BV): 26,
    (RD, HA): 10, (RD, FW): 18, (RD, MD): 20, (RD, BV): 26,
    (MD, HA): 12, (MD, FW): 22, (MD, RD): 20, (MD, BV): 15,
    (BV, HA): 19, (BV, FW): 25, (BV, RD): 25, (BV, MD): 13,
}

# Day start at Haight-Ashbury 09:00
day_start_loc = HA
day_start_time = minutes(9, 0)

# Friends constraints
friends = [
    {
        "name": "Sarah",
        "location": FW,
        "win_start": minutes(14, 45),
        "win_end": minutes(17, 30),
        "min_dur": 105
    },
    {
        "name": "Mary",
        "location": RD,
        "win_start": minutes(13, 0),
        "win_end": minutes(19, 15),
        "min_dur": 75
    },
    {
        "name": "Helen",
        "location": MD,
        "win_start": minutes(21, 45),
        "win_end": minutes(22, 30),
        "min_dur": 30
    },
    {
        "name": "Thomas",
        "location": BV,
        "win_start": minutes(15, 15),
        "win_end": minutes(18, 45),
        "min_dur": 120
    }
]

# Z3 Optimize
opt = Optimize()

# Variables per friend
meet = {}
start = {}
end = {}
for f in friends:
    n = f["name"]
    meet[n] = Bool(f"meet_{n}")
    start[n] = Int(f"start_{n}")
    end[n] = Int(f"end_{n}")

    # General domain
    opt.add(start[n] >= 0, end[n] >= 0, end[n] >= start[n])

    # If meeting: within window and minimum duration
    opt.add(Implies(meet[n],
                    And(
                        start[n] >= f["win_start"],
                        end[n] <= f["win_end"],
                        end[n] - start[n] >= f["min_dur"],
                        # Must be reachable from start location at 9:00
                        start[n] >= day_start_time + dist[(day_start_loc, f["location"])]
                    )))
    # If not meeting: collapse interval to 0
    opt.add(Implies(Not(meet[n]), And(start[n] == 0, end[n] == 0)))

# Pairwise ordering and travel feasibility
before = {}  # before[(p,q)] means p before q
for i in range(len(friends)):
    for j in range(i + 1, len(friends)):
        p = friends[i]["name"]
        q = friends[j]["name"]
        lp = friends[i]["location"]
        lq = friends[j]["location"]
        b = Bool(f"before_{p}_{q}")
        before[(p, q)] = b

        # If both are met, enforce that either p before q with travel time or q before p with travel time
        opt.add(Implies(And(meet[p], meet[q]),
                        Or(
                            And(b, end[p] + dist[(lp, lq)] <= start[q]),
                            And(Not(b), end[q] + dist[(lq, lp)] <= start[p])
                        )))

# Objectives:
# 1) Maximize number of friends met
count_meet = Sum([If(meet[f["name"]], 1, 0) for f in friends])
h1 = opt.maximize(count_meet)

# 2) Maximize total meeting duration
total_minutes = Sum([If(meet[f["name"]], end[f["name"]] - start[f["name"]], 0) for f in friends])
h2 = opt.maximize(total_minutes)

# Solve
if opt.check() != sat:
    # Should not happen with given data, but handle gracefully
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()

    # Extract scheduled meetings
    schedule = []
    for f in friends:
        n = f["name"]
        if is_true(m.eval(meet[n])):
            s = m.eval(start[n]).as_long()
            e = m.eval(end[n]).as_long()
            schedule.append({
                "person": n,
                "location": f["location"],
                "start": s,
                "end": e
            })

    # Sort by start time
    schedule.sort(key=lambda x: x["start"])

    # Build JSON itinerary
    itinerary = []
    for item in schedule:
        itinerary.append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": min_to_time(item["start"]),
            "end_time": min_to_time(item["end"])
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))