import json
from z3 import Int, Bool, If, And, Or, Not, Implies, Optimize, Sum, sat, is_true

# Helper to convert "H:MM"
def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times in minutes (directed)
travel = {
    "Haight-Ashbury": {
        "Fisherman's Wharf": 23,
        "Richmond District": 10,
        "Mission District": 11,
        "Bayview": 18
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22,
        "Richmond District": 18,
        "Mission District": 22,
        "Bayview": 26
    },
    "Richmond District": {
        "Haight-Ashbury": 10,
        "Fisherman's Wharf": 18,
        "Mission District": 20,
        "Bayview": 26
    },
    "Mission District": {
        "Haight-Ashbury": 12,
        "Fisherman's Wharf": 22,
        "Richmond District": 20,
        "Bayview": 15
    },
    "Bayview": {
        "Haight-Ashbury": 19,
        "Fisherman's Wharf": 25,
        "Richmond District": 25,
        "Mission District": 13
    }
}

def t(a, b):
    if a == b:
        return 0
    return travel[a][b]

# Input data
arrival_location = "Haight-Ashbury"
arrival_time = 9 * 60  # 9:00

friends = [
    {
        "name": "Sarah",
        "location": "Fisherman's Wharf",
        "avail_start": 14 * 60 + 45,  # 14:45
        "avail_end": 17 * 60 + 30,    # 17:30
        "min_duration": 105
    },
    {
        "name": "Mary",
        "location": "Richmond District",
        "avail_start": 13 * 60,       # 13:00
        "avail_end": 19 * 60 + 15,    # 19:15
        "min_duration": 75
    },
    {
        "name": "Helen",
        "location": "Mission District",
        "avail_start": 21 * 60 + 45,  # 21:45
        "avail_end": 22 * 60 + 30,    # 22:30
        "min_duration": 30
    },
    {
        "name": "Thomas",
        "location": "Bayview",
        "avail_start": 15 * 60 + 15,  # 15:15
        "avail_end": 18 * 60 + 45,    # 18:45
        "min_duration": 120
    }
]

n = len(friends)

# Z3 variables
starts = [Int(f"start_{i}") for i in range(n)]
ends = [Int(f"end_{i}") for i in range(n)]
selected = [Bool(f"selected_{i}") for i in range(n)]

opt = Optimize()

# Bounds and selection constraints
for i, f in enumerate(friends):
    # Time bounds
    opt.add(starts[i] >= 0, starts[i] <= 24 * 60)
    opt.add(ends[i] >= 0, ends[i] <= 24 * 60)
    # If selected, must be within availability windows and meet duration
    opt.add(Implies(selected[i], And(
        starts[i] >= f["avail_start"],
        ends[i] <= f["avail_end"],
        ends[i] > starts[i],
        ends[i] - starts[i] >= f["min_duration"]
    )))
    # If not selected, start=end=0 to avoid any unintended interactions
    opt.add(Implies(Not(selected[i]), And(starts[i] == 0, ends[i] == 0)))

# Non-overlap with travel feasibility between meetings
for i in range(n):
    for j in range(i + 1, n):
        li = friends[i]["location"]
        lj = friends[j]["location"]
        opt.add(Or(
            Not(selected[i]),
            Not(selected[j]),
            ends[i] + t(li, lj) <= starts[j],
            ends[j] + t(lj, li) <= starts[i]
        ))

# Anchoring constraint: each selected meeting must be reachable from arrival or another meeting
for i in range(n):
    li = friends[i]["location"]
    preds = []
    for j in range(n):
        if j == i:
            continue
        lj = friends[j]["location"]
        preds.append(And(selected[j], ends[j] + t(lj, li) <= starts[i]))
    from_start = starts[i] >= arrival_time + t(arrival_location, li)
    opt.add(Implies(selected[i], Or(from_start, Or(preds))))

# Objective: maximize number of meetings first, then total meeting time
sum_selected = Sum([If(selected[i], 1, 0) for i in range(n)])
sum_minutes = Sum([If(selected[i], ends[i] - starts[i], 0) for i in range(n)])
# Large weight to prioritize meeting count
score = sum_selected * 10000 + sum_minutes
opt.maximize(score)

# Solve
if opt.check() != sat:
    output = {"itinerary": []}
    print(json.dumps(output, ensure_ascii=False))
else:
    m = opt.model()
    itinerary = []
    for i, f in enumerate(friends):
        if is_true(m.evaluate(selected[i], model_completion=True)):
            s = m.evaluate(starts[i]).as_long()
            e = m.evaluate(ends[i]).as_long()
            itinerary.append({
                "action": "meet",
                "location": f["location"],
                "person": f["name"],
                "start_time": minutes_to_time(s),
                "end_time": minutes_to_time(e)
            })
    # Sort by start time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(':')[0]) * 60 + int(x["start_time"].split(':')[1])))
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))