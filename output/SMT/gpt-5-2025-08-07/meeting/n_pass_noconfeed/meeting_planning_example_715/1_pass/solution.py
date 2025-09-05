import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Travel times (in minutes), directional
T = {
    "Presidio": {
        "Marina District": 11,
        "The Castro": 21,
        "Fisherman's Wharf": 19,
        "Bayview": 31,
        "Pacific Heights": 11,
        "Mission District": 26,
        "Alamo Square": 19,
        "Golden Gate Park": 12,
    },
    "Marina District": {
        "Presidio": 10,
        "The Castro": 22,
        "Fisherman's Wharf": 10,
        "Bayview": 27,
        "Pacific Heights": 7,
        "Mission District": 20,
        "Alamo Square": 15,
        "Golden Gate Park": 18,
    },
    "The Castro": {
        "Presidio": 20,
        "Marina District": 21,
        "Fisherman's Wharf": 24,
        "Bayview": 19,
        "Pacific Heights": 16,
        "Mission District": 7,
        "Alamo Square": 8,
        "Golden Gate Park": 11,
    },
    "Fisherman's Wharf": {
        "Presidio": 17,
        "Marina District": 9,
        "The Castro": 27,
        "Bayview": 26,
        "Pacific Heights": 12,
        "Mission District": 22,
        "Alamo Square": 21,
        "Golden Gate Park": 25,
    },
    "Bayview": {
        "Presidio": 32,
        "Marina District": 27,
        "The Castro": 19,
        "Fisherman's Wharf": 25,
        "Pacific Heights": 23,
        "Mission District": 13,
        "Alamo Square": 16,
        "Golden Gate Park": 22,
    },
    "Pacific Heights": {
        "Presidio": 11,
        "Marina District": 6,
        "The Castro": 16,
        "Fisherman's Wharf": 13,
        "Bayview": 22,
        "Mission District": 15,
        "Alamo Square": 10,
        "Golden Gate Park": 15,
    },
    "Mission District": {
        "Presidio": 25,
        "Marina District": 19,
        "The Castro": 7,
        "Fisherman's Wharf": 22,
        "Bayview": 14,
        "Pacific Heights": 16,
        "Alamo Square": 11,
        "Golden Gate Park": 17,
    },
    "Alamo Square": {
        "Presidio": 17,
        "Marina District": 15,
        "The Castro": 8,
        "Fisherman's Wharf": 19,
        "Bayview": 16,
        "Pacific Heights": 10,
        "Mission District": 10,
        "Golden Gate Park": 9,
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Marina District": 16,
        "The Castro": 13,
        "Fisherman's Wharf": 24,
        "Bayview": 23,
        "Pacific Heights": 16,
        "Mission District": 17,
        "Alamo Square": 9,
    },
}

# Friends data
friends = [
    {
        "name": "Amanda",
        "location": "Marina District",
        "avail_start": minutes(14,45),
        "avail_end": minutes(19,30),
        "min_duration": 105
    },
    {
        "name": "Melissa",
        "location": "The Castro",
        "avail_start": minutes(9,30),
        "avail_end": minutes(17,0),
        "min_duration": 30
    },
    {
        "name": "Jeffrey",
        "location": "Fisherman's Wharf",
        "avail_start": minutes(12,45),
        "avail_end": minutes(18,45),
        "min_duration": 120
    },
    {
        "name": "Matthew",
        "location": "Bayview",
        "avail_start": minutes(10,15),
        "avail_end": minutes(13,15),
        "min_duration": 30
    },
    {
        "name": "Nancy",
        "location": "Pacific Heights",
        "avail_start": minutes(17,0),
        "avail_end": minutes(21,30),
        "min_duration": 105
    },
    {
        "name": "Karen",
        "location": "Mission District",
        "avail_start": minutes(17,30),
        "avail_end": minutes(20,30),
        "min_duration": 105
    },
    {
        "name": "Robert",
        "location": "Alamo Square",
        "avail_start": minutes(11,15),
        "avail_end": minutes(17,30),
        "min_duration": 120
    },
    {
        "name": "Joseph",
        "location": "Golden Gate Park",
        "avail_start": minutes(8,30),
        "avail_end": minutes(21,15),
        "min_duration": 105
    },
]

start_location = "Presidio"
start_time = minutes(9,0)

n = len(friends)

opt = Optimize()
opt.set(priority='lex')

# Decision variables
meet = [Bool(f"meet_{i}") for i in range(n)]
s = [Int(f"start_{i}") for i in range(n)]
e = [Int(f"end_{i}") for i in range(n)]

# Bounds and availability constraints
for i, fr in enumerate(friends):
    a = fr["avail_start"]
    b = fr["avail_end"]
    dmin = fr["min_duration"]
    loc = fr["location"]

    # Variable bounds
    opt.add(s[i] >= 0, s[i] <= 24*60)
    opt.add(e[i] >= 0, e[i] <= 24*60)

    # If meeting, stay within availability and minimum duration
    opt.add(Implies(meet[i], s[i] >= a))
    opt.add(Implies(meet[i], e[i] <= b))
    opt.add(Implies(meet[i], e[i] >= s[i] + dmin))

    # If not meeting, fix times to anchor (no effect on schedule)
    opt.add(Implies(Not(meet[i]), And(s[i] == a, e[i] == a)))

    # Must be reachable from start at 9:00
    travel_from_start = T[start_location][loc]
    opt.add(Implies(meet[i], s[i] >= start_time + travel_from_start))

# Pairwise non-overlap with travel times and implicit ordering
before = {}
for i in range(n):
    for j in range(i+1, n):
        bij = Bool(f"before_{i}_{j}")  # True if i before j
        before[(i,j)] = bij
        li = friends[i]["location"]
        lj = friends[j]["location"]
        tij = T[li][lj]
        tji = T[lj][li]

        # If both meetings occur, enforce an order with travel time
        opt.add(Implies(And(meet[i], meet[j]),
                        Or(And(bij, s[j] >= e[i] + tij),
                           And(Not(bij), s[i] >= e[j] + tji))))

# Objective: maximize number of friends met, then maximize total meeting time
total_met = Sum([If(meet[i], IntVal(1), IntVal(0)) for i in range(n)])
total_meeting_minutes = Sum([If(meet[i], e[i] - s[i], IntVal(0)) for i in range(n)])

opt.maximize(total_met)
opt.maximize(total_meeting_minutes)

if opt.check() != sat:
    # If unsat, output empty itinerary
    output = {"itinerary": []}
    print(json.dumps(output))
else:
    model = opt.model()
    chosen = []
    for i, fr in enumerate(friends):
        if is_true(model.evaluate(meet[i])):
            start_val = model.evaluate(s[i]).as_long()
            end_val = model.evaluate(e[i]).as_long()
            chosen.append({
                "person": fr["name"],
                "location": fr["location"],
                "start": start_val,
                "end": end_val
            })

    # Sort by start time
    chosen.sort(key=lambda x: x["start"])

    itinerary = []
    for item in chosen:
        itinerary.append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": fmt_time(item["start"]),
            "end_time": fmt_time(item["end"])
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))