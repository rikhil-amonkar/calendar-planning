import json
from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat, is_true

def t(h, m):  # minutes since midnight
    return h * 60 + m

def m2str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def big_or(lst):
    if not lst:
        return False
    return Or(*lst)

# Input data
start_location = "Sunset District"
arrival_time = t(9, 0)

people = {
    "Kevin": {
        "location": "Alamo Square",
        "start": t(8, 15),
        "end": t(21, 30),
        "min": 75,
    },
    "Kimberly": {
        "location": "Russian Hill",
        "start": t(8, 45),
        "end": t(12, 30),
        "min": 30,
    },
    "Joseph": {
        "location": "Presidio",
        "start": t(18, 30),
        "end": t(19, 15),
        "min": 45,
    },
    "Thomas": {
        "location": "Financial District",
        "start": t(19, 0),
        "end": t(21, 45),
        "min": 45,
    },
}

# Travel times (minutes)
travel = {
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Financial District"): 30,

    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Presidio"): 18,
    ("Alamo Square", "Financial District"): 17,

    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Financial District"): 11,

    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Financial District"): 23,

    ("Financial District", "Sunset District"): 31,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Russian Hill"): 10,
    ("Financial District", "Presidio"): 22,
}

def tt(a, b):
    return travel[(a, b)]

# Build SMT model
opt = Optimize()

names = list(people.keys())

meet = {n: Bool(f"meet_{n}") for n in names}
s = {n: Int(f"s_{n}") for n in names}
e = {n: Int(f"e_{n}") for n in names}

# Basic domain and availability constraints
for n in names:
    ws = people[n]["start"]
    we = people[n]["end"]
    min_d = people[n]["min"]

    opt.add(s[n] >= 0, e[n] >= 0, s[n] <= 24 * 60, e[n] <= 24 * 60)
    opt.add(
        If(
            meet[n],
            And(s[n] >= ws, e[n] <= we, e[n] - s[n] >= min_d, s[n] < e[n]),
            And(s[n] == 0, e[n] == 0)
        )
    )

# Pairwise non-overlap with travel time constraints
for i in range(len(names)):
    for j in range(i + 1, len(names)):
        ni = names[i]
        nj = names[j]
        li = people[ni]["location"]
        lj = people[nj]["location"]
        opt.add(
            Or(
                Not(meet[ni]),
                Not(meet[nj]),
                e[ni] + tt(li, lj) <= s[nj],
                e[nj] + tt(lj, li) <= s[ni]
            )
        )

# Reachability: each chosen meeting must be reachable from start or from a prior meeting
for ni in names:
    li = people[ni]["location"]
    preds = []
    for nj in names:
        if nj == ni:
            continue
        lj = people[nj]["location"]
        preds.append(And(meet[nj], e[nj] + tt(lj, li) <= s[ni]))
    opt.add(
        Or(
            Not(meet[ni]),
            Or(s[ni] >= arrival_time + tt(start_location, li), big_or(preds))
        )
    )

# Objective: maximize number of meetings; then minimize total meeting time; then minimize latest end time (makespan)
count_meet = Sum([If(meet[n], 1, 0) for n in names])
total_duration = Sum([If(meet[n], e[n] - s[n], 0) for n in names])
makespan = Int("makespan")
opt.add(makespan >= 0, makespan <= 24 * 60)
for n in names:
    opt.add(Or(Not(meet[n]), e[n] <= makespan))

opt.maximize(count_meet)
opt.minimize(total_duration)
opt.minimize(makespan)

result = {"itinerary": []}

if opt.check() == sat:
    m = opt.model()
    scheduled = []
    for n in names:
        if is_true(m.evaluate(meet[n], model_completion=True)):
            start_m = m.evaluate(s[n], model_completion=True).as_long()
            end_m = m.evaluate(e[n], model_completion=True).as_long()
            scheduled.append({
                "person": n,
                "location": people[n]["location"],
                "start": start_m,
                "end": end_m
            })
    scheduled.sort(key=lambda x: x["start"])
    for item in scheduled:
        result["itinerary"].append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": m2str(item["start"]),
            "end_time": m2str(item["end"])
        })

print(json.dumps(result, indent=2))