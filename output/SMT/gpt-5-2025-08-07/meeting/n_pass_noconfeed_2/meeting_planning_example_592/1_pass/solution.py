# SOLUTION:
# This program computes an optimal meeting schedule using the Z3 SMT solver
# to maximize the number of friends met given travel and availability constraints.
# It outputs a JSON itinerary.

from z3 import *
import json

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Locations
locations = [
    "North Beach",
    "Pacific Heights",
    "Chinatown",
    "Union Square",
    "Mission District",
    "Golden Gate Park",
    "Nob Hill",
]

# Travel times in minutes (asymmetric)
T = {
    ("North Beach","Pacific Heights"): 8,
    ("North Beach","Chinatown"): 6,
    ("North Beach","Union Square"): 7,
    ("North Beach","Mission District"): 18,
    ("North Beach","Golden Gate Park"): 22,
    ("North Beach","Nob Hill"): 7,

    ("Pacific Heights","North Beach"): 9,
    ("Pacific Heights","Chinatown"): 11,
    ("Pacific Heights","Union Square"): 12,
    ("Pacific Heights","Mission District"): 15,
    ("Pacific Heights","Golden Gate Park"): 15,
    ("Pacific Heights","Nob Hill"): 8,

    ("Chinatown","North Beach"): 3,
    ("Chinatown","Pacific Heights"): 10,
    ("Chinatown","Union Square"): 7,
    ("Chinatown","Mission District"): 18,
    ("Chinatown","Golden Gate Park"): 23,
    ("Chinatown","Nob Hill"): 8,

    ("Union Square","North Beach"): 10,
    ("Union Square","Pacific Heights"): 15,
    ("Union Square","Chinatown"): 7,
    ("Union Square","Mission District"): 14,
    ("Union Square","Golden Gate Park"): 22,
    ("Union Square","Nob Hill"): 9,

    ("Mission District","North Beach"): 17,
    ("Mission District","Pacific Heights"): 16,
    ("Mission District","Chinatown"): 16,
    ("Mission District","Union Square"): 15,
    ("Mission District","Golden Gate Park"): 17,
    ("Mission District","Nob Hill"): 12,

    ("Golden Gate Park","North Beach"): 24,
    ("Golden Gate Park","Pacific Heights"): 16,
    ("Golden Gate Park","Chinatown"): 23,
    ("Golden Gate Park","Union Square"): 22,
    ("Golden Gate Park","Mission District"): 17,
    ("Golden Gate Park","Nob Hill"): 20,

    ("Nob Hill","North Beach"): 8,
    ("Nob Hill","Pacific Heights"): 8,
    ("Nob Hill","Chinatown"): 6,
    ("Nob Hill","Union Square"): 7,
    ("Nob Hill","Mission District"): 13,
    ("Nob Hill","Golden Gate Park"): 17,
}

def travel(a, b):
    if a == b:
        return 0
    return T[(a, b)]

# People, locations, availability windows, minimum meeting durations
friends = [
    {
        "name": "James",
        "location": "Pacific Heights",
        "start": minutes(20, 0),   # 20:00
        "end": minutes(22, 0),     # 22:00
        "min_duration": 120,
    },
    {
        "name": "Robert",
        "location": "Chinatown",
        "start": minutes(12, 15),  # 12:15
        "end": minutes(16, 45),    # 16:45
        "min_duration": 90,
    },
    {
        "name": "Jeffrey",
        "location": "Union Square",
        "start": minutes(9, 30),   # 9:30
        "end": minutes(15, 30),    # 15:30
        "min_duration": 120,
    },
    {
        "name": "Carol",
        "location": "Mission District",
        "start": minutes(18, 15),  # 18:15
        "end": minutes(21, 15),    # 21:15
        "min_duration": 15,
    },
    {
        "name": "Mark",
        "location": "Golden Gate Park",
        "start": minutes(11, 30),  # 11:30
        "end": minutes(17, 45),    # 17:45
        "min_duration": 15,
    },
    {
        "name": "Sandra",
        "location": "Nob Hill",
        "start": minutes(8, 0),    # 8:00
        "end": minutes(15, 30),    # 15:30
        "min_duration": 15,
    },
]

start_location = "North Beach"
arrival_time = minutes(9, 0)  # 9:00

n = len(friends)

# Z3 variables
opt = Optimize()

meet = [Bool(f"meet_{i}") for i in range(n)]
svar = [Int(f"start_{i}") for i in range(n)]
evar = [Int(f"end_{i}") for i in range(n)]
dvar = [Int(f"dur_{i}") for i in range(n)]

# Bounds for times
for i in range(n):
    opt.add(svar[i] >= 0, svar[i] <= 24*60)
    opt.add(evar[i] >= 0, evar[i] <= 24*60)
    opt.add(dvar[i] >= 0, dvar[i] <= 24*60)

# Availability and duration constraints
for i, f in enumerate(friends):
    wlen = f["end"] - f["start"]
    opt.add(Implies(meet[i], And(
        svar[i] >= f["start"],
        evar[i] <= f["end"],
        dvar[i] == evar[i] - svar[i],
        dvar[i] >= f["min_duration"],
        dvar[i] <= wlen
    )))
    # If not meeting, zero times
    opt.add(Implies(Not(meet[i]), And(
        dvar[i] == 0,
        svar[i] == 0,
        evar[i] == 0
    )))
    # Must be reachable from initial location at arrival time (loose lower bound)
    # This does not force being first; it's simply a global lower bound.
    opt.add(Implies(meet[i], svar[i] >= arrival_time + travel(start_location, f["location"])))

# Pairwise sequencing with travel times
before_bools = {}
for i in range(n):
    for j in range(i+1, n):
        b = Bool(f"before_{i}_{j}")  # True: i before j; False: j before i
        before_bools[(i, j)] = b
        ti_j = travel(friends[i]["location"], friends[j]["location"])
        tj_i = travel(friends[j]["location"], friends[i]["location"])
        opt.add(Implies(And(meet[i], meet[j], b), evar[i] + ti_j <= svar[j]))
        opt.add(Implies(And(meet[i], meet[j], Not(b)), evar[j] + tj_i <= svar[i]))
        # If either not meeting, no constraint needed; guarded already

# Objective: maximize number of meetings
num_met = Sum([If(meet[i], 1, 0) for i in range(n)])
opt.maximize(num_met)

# Secondary: maximize total duration across meetings
total_duration = Sum([dvar[i] for i in range(n)])
opt.maximize(total_duration)

# Tertiary: minimize makespan (end time of last meeting)
makespan = Int("makespan")
opt.add(makespan >= 0, makespan <= 24*60)
for i in range(n):
    opt.add(makespan >= evar[i])  # evar[i] == 0 if not meeting
opt.minimize(makespan)

# Solve
if opt.check() != sat:
    # Fallback: output empty itinerary
    result = {"itinerary": []}
    print(json.dumps(result))
    exit(0)

m = opt.model()

# Extract meetings
itinerary = []
for i, f in enumerate(friends):
    if is_true(m.evaluate(meet[i])):
        s = m.evaluate(svar[i]).as_long()
        e = m.evaluate(evar[i]).as_long()
        itinerary.append({
            "action": "meet",
            "location": f["location"],
            "person": f["name"],
            "start_time": fmt_time(s),
            "end_time": fmt_time(e)
        })

# Sort by start time
itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0])*60 + int(x["start_time"].split(":")[1])))

# Output JSON
output = {"itinerary": itinerary}
print(json.dumps(output))