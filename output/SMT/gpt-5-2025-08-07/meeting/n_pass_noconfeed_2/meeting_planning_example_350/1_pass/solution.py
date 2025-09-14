import json
from z3 import *

def hm(h, m):
    return h * 60 + m

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Data setup
locations = ["Bayview", "Pacific Heights", "Mission District", "Haight-Ashbury", "Financial District"]

travel = {
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Financial District"): 19,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Financial District"): 13,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Financial District"): 17,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Haight-Ashbury"): 19,
}

people = {
    "Mary": {
        "location": "Pacific Heights",
        "window_start": hm(10, 0),
        "window_end": hm(19, 0),
        "min_duration": 45
    },
    "Lisa": {
        "location": "Mission District",
        "window_start": hm(20, 30),
        "window_end": hm(22, 0),
        "min_duration": 75
    },
    "Betty": {
        "location": "Haight-Ashbury",
        "window_start": hm(7, 15),
        "window_end": hm(17, 15),
        "min_duration": 90
    },
    "Charles": {
        "location": "Financial District",
        "window_start": hm(11, 15),
        "window_end": hm(15, 0),
        "min_duration": 120
    },
}

start_location = "Bayview"
arrival_time = hm(9, 0)
day_end = hm(24, 0)

# Z3 variables
sel = {}
s = {}
d = {}
e = {}

opt = Optimize()
opt.set(priority='lex')

for p in people:
    sel[p] = Bool(f"sel_{p}")
    s[p] = Int(f"s_{p}")
    d[p] = Int(f"d_{p}")
    e[p] = Int(f"e_{p}")

for p, info in people.items():
    # Bounds
    opt.add(s[p] >= 0, s[p] <= day_end)
    opt.add(d[p] >= 0, d[p] <= day_end)
    opt.add(e[p] >= 0, e[p] <= day_end)
    opt.add(e[p] == s[p] + d[p])

    # If not selected, duration is 0
    opt.add(Implies(Not(sel[p]), d[p] == 0))

    # If selected, enforce window and min durations
    ws = info["window_start"]
    we = info["window_end"]
    min_d = info["min_duration"]
    opt.add(Implies(sel[p], And(
        s[p] >= ws,
        e[p] <= we,
        d[p] >= min_d,
        d[p] <= we - ws
    )))

# Non-overlap with travel time between any two selected meetings
people_list = list(people.keys())
for i in range(len(people_list)):
    for j in range(i + 1, len(people_list)):
        p = people_list[i]
        q = people_list[j]
        lp = people[p]["location"]
        lq = people[q]["location"]
        tpq = travel[(lp, lq)]
        tqp = travel[(lq, lp)]
        opt.add(Or(
            Not(sel[p]), Not(sel[q]),
            e[p] + tpq <= s[q],
            e[q] + tqp <= s[p]
        ))

# Connectivity: each selected meeting must be reachable either from start or from a prior meeting
for p in people:
    lp = people[p]["location"]
    from_start = s[p] >= arrival_time + travel[(start_location, lp)]
    preds = []
    for q in people:
        if q == p:
            continue
        lq = people[q]["location"]
        preds.append(And(sel[q], e[q] + travel[(lq, lp)] <= s[p]))
    if preds:
        opt.add(Implies(sel[p], Or(from_start, Or(preds))))
    else:
        opt.add(Implies(sel[p], from_start))

# Objectives
total_meetings = Sum([If(sel[p], 1, 0) for p in people])
total_duration = Sum([d[p] for p in people])  # since d[p]==0 if not selected

opt.maximize(total_meetings)
opt.maximize(total_duration)

# Solve
if opt.check() != sat:
    # Fallback: no feasible schedule
    result = {"itinerary": []}
    print(json.dumps(result))
else:
    model = opt.model()
    itinerary = []
    for p in people:
        if is_true(model.eval(sel[p])):
            start_min = model.eval(s[p]).as_long()
            end_min = model.eval(e[p]).as_long()
            itinerary.append({
                "action": "meet",
                "location": people[p]["location"],
                "person": p,
                "start_time": minutes_to_str(start_min),
                "end_time": minutes_to_str(end_min)
            })
    # Sort by start time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))
    print(json.dumps({"itinerary": itinerary}))