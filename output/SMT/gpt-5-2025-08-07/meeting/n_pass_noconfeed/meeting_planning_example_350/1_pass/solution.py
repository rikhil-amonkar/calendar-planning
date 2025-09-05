import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def to_time_str(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h}:{m:02d}"

# Data: Locations and travel times (in minutes)
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

def t(a, b):
    if a == b:
        return 0
    return travel[(a, b)]

# People data: location, availability window, minimum meeting duration
people = {
    "Mary": {
        "location": "Pacific Heights",
        "avail_start": minutes(10, 0),
        "avail_end": minutes(19, 0),
        "min_duration": 45,
    },
    "Lisa": {
        "location": "Mission District",
        "avail_start": minutes(20, 30),
        "avail_end": minutes(22, 0),
        "min_duration": 75,
    },
    "Betty": {
        "location": "Haight-Ashbury",
        "avail_start": minutes(7, 15),
        "avail_end": minutes(17, 15),
        "min_duration": 90,
    },
    "Charles": {
        "location": "Financial District",
        "avail_start": minutes(11, 15),
        "avail_end": minutes(15, 0),
        "min_duration": 120,
    },
}

start_location = "Bayview"
start_time = minutes(9, 0)

names = list(people.keys())

# Z3 variables
start = {p: Int(f"start_{p}") for p in names}
end = {p: Int(f"end_{p}") for p in names}
dur = {p: Int(f"dur_{p}") for p in names}
met = {p: Bool(f"met_{p}") for p in names}

# Pairwise ordering booleans
before = {}
for i in range(len(names)):
    for j in range(i + 1, len(names)):
        p, q = names[i], names[j]
        before[(p, q)] = Bool(f"before_{p}_{q}")
        before[(q, p)] = Bool(f"before_{q}_{p}")

opt = Optimize()

# Bounds and meeting constraints
for p in names:
    # Domain bounds
    opt.add(start[p] >= 0, start[p] <= 24 * 60)
    opt.add(end[p] >= 0, end[p] <= 24 * 60)
    opt.add(dur[p] >= 0, dur[p] <= 24 * 60)
    opt.add(end[p] == start[p] + dur[p])

    # If met: must be within availability and meet minimum duration
    aps = people[p]["avail_start"]
    ape = people[p]["avail_end"]
    mind = people[p]["min_duration"]
    opt.add(Implies(met[p], start[p] >= aps))
    opt.add(Implies(met[p], end[p] <= ape))
    opt.add(Implies(met[p], dur[p] >= mind))

    # If not met: duration is zero (ensures it isn't used)
    opt.add(Implies(Not(met[p]), dur[p] == 0))

# Ordering and travel constraints
for i in range(len(names)):
    for j in range(i + 1, len(names)):
        p, q = names[i], names[j]
        bpq = before[(p, q)]
        bqp = before[(q, p)]

        # If both met, exactly one ordering; otherwise, both false
        opt.add(Implies(And(met[p], met[q]), And(Or(bpq, bqp), Not(And(bpq, bqp)))))
        opt.add(Implies(Not(And(met[p], met[q])), And(Not(bpq), Not(bqp))))

        # Travel and non-overlap constraints tied to ordering
        opt.add(Implies(And(met[p], met[q], bpq), start[q] >= end[p] + t(people[p]["location"], people[q]["location"])))
        opt.add(Implies(And(met[p], met[q], bqp), start[p] >= end[q] + t(people[q]["location"], people[p]["location"])))

# First meeting constraint: from starting point (Bayview at 9:00)
for p in names:
    preds = []
    for q in names:
        if q == p:
            continue
        preds.append(And(met[p], met[q], before[(q, p)]))
    has_pred = Or(preds) if preds else BoolVal(False)
    opt.add(Implies(And(met[p], Not(has_pred)), start[p] >= start_time + t(start_location, people[p]["location"])))

# Objectives: maximize number of meetings, then total meeting time
count_met = Sum([If(met[p], IntVal(1), IntVal(0)) for p in names])
total_meeting_time = Sum([If(met[p], dur[p], IntVal(0)) for p in names])

opt.maximize(count_met)
opt.maximize(total_meeting_time)

# Solve
if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
    exit(0)

model = opt.model()

# Build itinerary
entries = []
for p in names:
    if is_true(model.eval(met[p], model_completion=True)):
        s = model.eval(start[p], model_completion=True).as_long()
        e = model.eval(end[p], model_completion=True).as_long()
        entries.append({
            "person": p,
            "location": people[p]["location"],
            "start": s,
            "end": e
        })

# Sort by start time
entries.sort(key=lambda x: x["start"])

itinerary = []
for e in entries:
    itinerary.append({
        "action": "meet",
        "location": e["location"],
        "person": e["person"],
        "start_time": to_time_str(e["start"]),
        "end_time": to_time_str(e["end"]),
    })

print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))