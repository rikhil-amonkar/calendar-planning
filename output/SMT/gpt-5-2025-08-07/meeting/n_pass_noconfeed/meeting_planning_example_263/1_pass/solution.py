"""SOLUTION:"""
from z3 import *
import json

def hm_to_min(h, m):
    return h * 60 + m

def min_to_hm(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Input data (constraints and travel times)
start_location = "Bayview"
start_time = hm_to_min(9, 0)  # 9:00

people = ["Betty", "Karen", "Anthony"]
locations = {
    "Betty": "Embarcadero",
    "Karen": "Fisherman's Wharf",
    "Anthony": "Financial District",
}
availability = {
    "Betty": (hm_to_min(19, 45), hm_to_min(21, 45)),   # 7:45PM - 9:45PM
    "Karen": (hm_to_min(8, 45), hm_to_min(15, 0)),     # 8:45AM - 3:00PM
    "Anthony": (hm_to_min(9, 15), hm_to_min(21, 30)),  # 9:15AM - 9:30PM
}
min_duration = {
    "Betty": 15,
    "Karen": 30,
    "Anthony": 105,
}
# Directed travel times in minutes
travel = {
    "Bayview": {
        "Embarcadero": 19,
        "Fisherman's Wharf": 25,
        "Financial District": 19,
    },
    "Embarcadero": {
        "Bayview": 21,
        "Fisherman's Wharf": 6,
        "Financial District": 5,
    },
    "Fisherman's Wharf": {
        "Bayview": 26,
        "Embarcadero": 8,
        "Financial District": 11,
    },
    "Financial District": {
        "Bayview": 19,
        "Embarcadero": 4,
        "Fisherman's Wharf": 10,
    }
}

def t(a, b):
    return travel[a][b]

# Z3 variables
s = {p: Int(f"{p}_start") for p in people}
e = {p: Int(f"{p}_end") for p in people}
met = {p: Bool(f"{p}_met") for p in people}
first = {p: Bool(f"{p}_first") for p in people}

opt = Optimize()
opt.set(priority='lex')

# Basic constraints per person
for p in people:
    a_start, a_end = availability[p]
    min_dur = min_duration[p]
    # If met, enforce availability and duration
    opt.add(Implies(met[p],
                    And(s[p] >= a_start,
                        e[p] <= a_end,
                        e[p] > s[p],
                        e[p] - s[p] >= min_dur)))
    # If not met, collapse times to zero and not first
    opt.add(Implies(Not(met[p]), And(s[p] == 0, e[p] == 0, Not(first[p]))))
    # 'first' implies met
    opt.add(Implies(first[p], met[p]))
    # If first, ensure reachable from start location
    opt.add(Implies(first[p], s[p] >= start_time + t(start_location, locations[p])))

# Exactly one 'first' if at least one met, else none
sum_met = Sum([If(met[p], 1, 0) for p in people])
sum_first = Sum([If(first[p], 1, 0) for p in people])
opt.add(sum_first == If(sum_met > 0, 1, 0))

# Pairwise non-overlap with travel disjunctions
for i in range(len(people)):
    for j in range(i + 1, len(people)):
        p, q = people[i], people[j]
        lp, lq = locations[p], locations[q]
        opt.add(Implies(And(met[p], met[q]),
                        Or(e[p] + t(lp, lq) <= s[q],
                           e[q] + t(lq, lp) <= s[p])))

# Connectivity: every met person is either first or has at least one predecessor that allows travel
for p in people:
    preds = []
    for q in people:
        if q == p:
            continue
        preds.append(And(met[q], e[q] + t(locations[q], locations[p]) <= s[p]))
    opt.add(Implies(met[p], Or(first[p], Or(preds))))

# Objectives:
# 1) Maximize number of friends met
h1 = opt.maximize(sum_met)
# 2) Maximize total meeting time
total_meeting_time = Sum([If(met[p], e[p] - s[p], 0) for p in people])
h2 = opt.maximize(total_meeting_time)

# Solve
if opt.check() != sat:
    # If somehow unsat (shouldn't happen), output empty itinerary
    result = {"itinerary": []}
    print(json.dumps(result, ensure_ascii=False))
else:
    m = opt.model()
    events = []
    for p in people:
        if is_true(m.evaluate(met[p])):
            sp = m.evaluate(s[p]).as_long()
            ep = m.evaluate(e[p]).as_long()
            events.append({
                "person": p,
                "location": locations[p],
                "start": sp,
                "end": ep
            })
    # Sort by start times
    events.sort(key=lambda evt: evt["start"])
    itinerary = []
    for evt in events:
        itinerary.append({
            "action": "meet",
            "location": evt["location"],
            "person": evt["person"],
            "start_time": min_to_hm(evt["start"]),
            "end_time": min_to_hm(evt["end"]),
        })
    result = {"itinerary": itinerary}
    print(json.dumps(result, ensure_ascii=False))