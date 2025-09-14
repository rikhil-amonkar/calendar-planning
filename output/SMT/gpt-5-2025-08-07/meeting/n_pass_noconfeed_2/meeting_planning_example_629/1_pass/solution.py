"""SOLUTION:"""
import json
from z3 import Optimize, Int, Bool, If, And, Or, Not, Implies, Sum, sat

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Locations
locations = [
    "Russian Hill",
    "Presidio",
    "Chinatown",
    "Pacific Heights",
    "Richmond District",
    "Fisherman's Wharf",
    "Golden Gate Park",
    "Bayview",
]

# Directed travel times (in minutes)
travel = {}
def set_travel(a, b, t):
    travel[(a, b)] = t

# Fill in travel times as provided
set_travel("Russian Hill", "Presidio", 14)
set_travel("Russian Hill", "Chinatown", 9)
set_travel("Russian Hill", "Pacific Heights", 7)
set_travel("Russian Hill", "Richmond District", 14)
set_travel("Russian Hill", "Fisherman's Wharf", 7)
set_travel("Russian Hill", "Golden Gate Park", 21)
set_travel("Russian Hill", "Bayview", 23)

set_travel("Presidio", "Russian Hill", 14)
set_travel("Presidio", "Chinatown", 21)
set_travel("Presidio", "Pacific Heights", 11)
set_travel("Presidio", "Richmond District", 7)
set_travel("Presidio", "Fisherman's Wharf", 19)
set_travel("Presidio", "Golden Gate Park", 12)
set_travel("Presidio", "Bayview", 31)

set_travel("Chinatown", "Russian Hill", 7)
set_travel("Chinatown", "Presidio", 19)
set_travel("Chinatown", "Pacific Heights", 10)
set_travel("Chinatown", "Richmond District", 20)
set_travel("Chinatown", "Fisherman's Wharf", 8)
set_travel("Chinatown", "Golden Gate Park", 23)
set_travel("Chinatown", "Bayview", 22)

set_travel("Pacific Heights", "Russian Hill", 7)
set_travel("Pacific Heights", "Presidio", 11)
set_travel("Pacific Heights", "Chinatown", 11)
set_travel("Pacific Heights", "Richmond District", 12)
set_travel("Pacific Heights", "Fisherman's Wharf", 13)
set_travel("Pacific Heights", "Golden Gate Park", 15)
set_travel("Pacific Heights", "Bayview", 22)

set_travel("Richmond District", "Russian Hill", 13)
set_travel("Richmond District", "Presidio", 7)
set_travel("Richmond District", "Chinatown", 20)
set_travel("Richmond District", "Pacific Heights", 10)
set_travel("Richmond District", "Fisherman's Wharf", 18)
set_travel("Richmond District", "Golden Gate Park", 9)
set_travel("Richmond District", "Bayview", 26)

set_travel("Fisherman's Wharf", "Russian Hill", 7)
set_travel("Fisherman's Wharf", "Presidio", 17)
set_travel("Fisherman's Wharf", "Chinatown", 12)
set_travel("Fisherman's Wharf", "Pacific Heights", 12)
set_travel("Fisherman's Wharf", "Richmond District", 18)
set_travel("Fisherman's Wharf", "Golden Gate Park", 25)
set_travel("Fisherman's Wharf", "Bayview", 26)

set_travel("Golden Gate Park", "Russian Hill", 19)
set_travel("Golden Gate Park", "Presidio", 11)
set_travel("Golden Gate Park", "Chinatown", 23)
set_travel("Golden Gate Park", "Pacific Heights", 16)
set_travel("Golden Gate Park", "Richmond District", 7)
set_travel("Golden Gate Park", "Fisherman's Wharf", 24)
set_travel("Golden Gate Park", "Bayview", 23)

set_travel("Bayview", "Russian Hill", 23)
set_travel("Bayview", "Presidio", 31)
set_travel("Bayview", "Chinatown", 18)
set_travel("Bayview", "Pacific Heights", 23)
set_travel("Bayview", "Richmond District", 25)
set_travel("Bayview", "Fisherman's Wharf", 25)
set_travel("Bayview", "Golden Gate Park", 22)

# Ensure zero self-travel
for a in locations:
    set_travel(a, a, 0)

# Friends with constraints
friends = [
    {
        "name": "Matthew",
        "location": "Presidio",
        "start": minutes(11, 0),
        "end": minutes(21, 0),
        "min_dur": 90,
    },
    {
        "name": "Margaret",
        "location": "Chinatown",
        "start": minutes(9, 15),
        "end": minutes(18, 45),
        "min_dur": 90,
    },
    {
        "name": "Nancy",
        "location": "Pacific Heights",
        "start": minutes(14, 15),
        "end": minutes(17, 0),
        "min_dur": 15,
    },
    {
        "name": "Helen",
        "location": "Richmond District",
        "start": minutes(19, 45),
        "end": minutes(22, 0),
        "min_dur": 60,
    },
    {
        "name": "Rebecca",
        "location": "Fisherman's Wharf",
        "start": minutes(21, 15),
        "end": minutes(22, 15),
        "min_dur": 60,
    },
    {
        "name": "Kimberly",
        "location": "Golden Gate Park",
        "start": minutes(13, 0),
        "end": minutes(16, 30),
        "min_dur": 120,
    },
    {
        "name": "Kenneth",
        "location": "Bayview",
        "start": minutes(14, 30),
        "end": minutes(18, 0),
        "min_dur": 60,
    },
]

origin_location = "Russian Hill"
arrival_time = minutes(9, 0)
day_end = minutes(23, 59)

opt = Optimize()
opt.set(priority='lex')

N = len(friends)

# Decision variables
meet = []
start_vars = []
end_vars = []
for i in range(N):
    meet_i = Bool(f"meet_{i}")
    s_i = Int(f"start_{i}")
    e_i = Int(f"end_{i}")
    meet.append(meet_i)
    start_vars.append(s_i)
    end_vars.append(e_i)
    # Domain bounds
    opt.add(s_i >= 0, s_i <= day_end)
    opt.add(e_i >= 0, e_i <= day_end)
    # If meeting, respect availability and min duration
    opt.add(Implies(meet_i, And(
        s_i >= friends[i]["start"],
        e_i <= friends[i]["end"],
        e_i - s_i >= friends[i]["min_dur"]
    )))
    # If not meeting, set zero-length interval (arbitrary)
    opt.add(Implies(Not(meet_i), e_i == s_i))
    # Origin travel feasibility (lower bound)
    loc_i = friends[i]["location"]
    origin_travel = travel[(origin_location, loc_i)]
    opt.add(Implies(meet_i, s_i >= arrival_time + origin_travel))

# Pairwise sequencing with travel times
before = {}  # order variables b_ij meaning i before j
for i in range(N):
    for j in range(i + 1, N):
        b_ij = Bool(f"before_{i}_{j}")
        before[(i, j)] = b_ij
        li = friends[i]["location"]
        lj = friends[j]["location"]
        tij = travel[(li, lj)]
        tji = travel[(lj, li)]
        # Only active if both meetings occur; otherwise unconstrained
        opt.add(Implies(And(meet[i], meet[j], b_ij), end_vars[i] + tij <= start_vars[j]))
        opt.add(Implies(And(meet[i], meet[j], Not(b_ij)), end_vars[j] + tji <= start_vars[i]))

# Objectives
num_met = Sum([If(meet[i], 1, 0) for i in range(N)])
total_meeting_minutes = Sum([If(meet[i], end_vars[i] - start_vars[i], 0) for i in range(N)])
opt.maximize(num_met)
opt.maximize(total_meeting_minutes)

# Solve
if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
    raise SystemExit(0)

m = opt.model()

# Extract and sort meetings
meetings = []
for i in range(N):
    if m.evaluate(meet[i], model_completion=True):
        s = m.evaluate(start_vars[i]).as_long()
        e = m.evaluate(end_vars[i]).as_long()
        meetings.append({
            "person": friends[i]["name"],
            "location": friends[i]["location"],
            "start": s,
            "end": e
        })

meetings.sort(key=lambda x: x["start"])

# Build JSON output
output = {"itinerary": []}
for mee in meetings:
    output["itinerary"].append({
        "action": "meet",
        "location": mee["location"],
        "person": mee["person"],
        "start_time": fmt_time(mee["start"]),
        "end_time": fmt_time(mee["end"])
    })

print(json.dumps(output, ensure_ascii=False))