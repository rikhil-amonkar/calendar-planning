"""SOLUTION:"""
from z3 import *
import json

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Data
locations = [
    "Richmond District",
    "Sunset District",
    "Haight-Ashbury",
    "Mission District",
    "Golden Gate Park",
]

# Directed travel times in minutes (as given)
T = {
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Golden Gate Park"): 9,

    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Golden Gate Park"): 11,

    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Golden Gate Park"): 7,

    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Golden Gate Park"): 17,

    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,
}

# Add zero-cost for same-location travel
for loc in locations:
    T[(loc, loc)] = 0

start_at_richmond = minutes(9, 0)

# Friends data
friends = {
    "Sarah": {
        "location": "Sunset District",
        "avail_start": minutes(10, 45),
        "avail_end": minutes(19, 0),
        "min_dur": 30
    },
    "Richard": {
        "location": "Haight-Ashbury",
        "avail_start": minutes(11, 45),
        "avail_end": minutes(15, 45),
        "min_dur": 90
    },
    "Elizabeth": {
        "location": "Mission District",
        "avail_start": minutes(11, 0),
        "avail_end": minutes(17, 15),
        "min_dur": 120
    },
    "Michelle": {
        "location": "Golden Gate Park",
        "avail_start": minutes(18, 15),
        "avail_end": minutes(20, 45),
        "min_dur": 90
    },
}

names = list(friends.keys())

# Z3 variables
opt = Optimize()
opt.set("priority", "lex")

meet = {n: Bool(f"meet_{n}") for n in names}
start = {n: Int(f"start_{n}") for n in names}
end = {n: Int(f"end_{n}") for n in names}
dur = {n: Int(f"dur_{n}") for n in names}
first = {n: Bool(f"first_{n}") for n in names}
last = {n: Bool(f"last_{n}") for n in names}

next_edge = {}
for i in names:
    for j in names:
        if i == j:
            continue
        next_edge[(i, j)] = Bool(f"next_{i}_to_{j}")

# Base constraints for time vars
for n in names:
    fi = friends[n]
    # domains
    opt.add(start[n] >= 0, end[n] >= 0, dur[n] >= 0)
    # meeting windows and durations
    opt.add(
        If(meet[n],
           And(
               start[n] >= fi["avail_start"],
               end[n] <= fi["avail_end"],
               dur[n] == end[n] - start[n],
               dur[n] >= fi["min_dur"]
           ),
           And(
               start[n] == 0,
               end[n] == 0,
               dur[n] == 0,
               Not(first[n]),
               Not(last[n])
           ))
    )
    # First implies meet; Last implies meet
    opt.add(Implies(first[n], meet[n]))
    opt.add(Implies(last[n], meet[n]))

# Next-edge implies both endpoints are met
for (i, j), var in next_edge.items():
    opt.add(Implies(var, And(meet[i], meet[j])))

# In-degree and out-degree constraints and path consistency
for n in names:
    out_vars = [next_edge[(n, j)] for j in names if j != n]
    in_vars = [next_edge[(i, n)] for i in names if i != n]

    out_sum = Sum([If(v, 1, 0) for v in out_vars]) if out_vars else IntVal(0)
    in_sum = Sum([If(v, 1, 0) for v in in_vars]) if in_vars else IntVal(0)

    # If not meeting n, no incident edges and not first/last already enforced above
    opt.add(Implies(Not(meet[n]), And(out_sum == 0, in_sum == 0)))

    # If meeting and not last, exactly one outgoing; if last, none
    opt.add(Implies(And(meet[n], Not(last[n])), out_sum == 1))
    opt.add(Implies(last[n], out_sum == 0))

    # If meeting and not first, exactly one incoming; if first, none
    opt.add(Implies(And(meet[n], Not(first[n])), in_sum == 1))
    opt.add(Implies(first[n], in_sum == 0))

# Travel time constraints between consecutive meetings
for (i, j), var in next_edge.items():
    li = friends[i]["location"]
    lj = friends[j]["location"]
    t = T[(li, lj)]
    opt.add(Implies(var, start[j] >= end[i] + t))

# Travel time for the first meeting from Richmond
for n in names:
    loc = friends[n]["location"]
    t0 = T[("Richmond District", loc)]
    opt.add(Implies(first[n], start[n] >= start_at_richmond + t0))

# Single path over selected meetings: counts of first/last/edges
total_meet = Sum([If(meet[n], 1, 0) for n in names])
total_first = Sum([If(first[n], 1, 0) for n in names])
total_last = Sum([If(last[n], 1, 0) for n in names])
total_edges = Sum([If(v, 1, 0) for v in next_edge.values()]) if next_edge else IntVal(0)

opt.add(Implies(total_meet == 0, And(total_first == 0, total_last == 0, total_edges == 0)))
opt.add(Implies(total_meet > 0, And(total_first == 1, total_last == 1, total_edges == total_meet - 1)))

# Objectives:
# 1) Maximize number of friends met
opt.maximize(total_meet)
# 2) Maximize total meeting time
opt.maximize(Sum([dur[n] for n in names]))

# Solve
if opt.check() != sat:
    result = {"itinerary": []}
    print(json.dumps(result))
    raise SystemExit(0)

model = opt.model()

# Build itinerary from model
entries = []
for n in names:
    if is_true(model.evaluate(meet[n])):
        s = model.evaluate(start[n]).as_long()
        e = model.evaluate(end[n]).as_long()
        entries.append({
            "person": n,
            "location": friends[n]["location"],
            "start_minutes": s,
            "end_minutes": e
        })

# Sort by start time
entries.sort(key=lambda x: x["start_minutes"])

# Format to JSON schema
itinerary = []
for item in entries:
    itinerary.append({
        "action": "meet",
        "location": item["location"],
        "person": item["person"],
        "start_time": fmt_time(item["start_minutes"]),
        "end_time": fmt_time(item["end_minutes"])
    })

print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))