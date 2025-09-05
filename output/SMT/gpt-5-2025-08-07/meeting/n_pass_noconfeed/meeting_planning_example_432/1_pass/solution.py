from z3 import *
import json

# Time formatting helper
def minutes_to_hhmm(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Locations
GGP = "Golden Gate Park"
FISH = "Fisherman's Wharf"
BAY = "Bayview"
MIS = "Mission District"
EMB = "Embarcadero"
FIN = "Financial District"

locations = [GGP, FISH, BAY, MIS, EMB, FIN]

# Travel times (minutes), directional as given
travel = {
    GGP: {FISH: 24, BAY: 23, MIS: 17, EMB: 25, FIN: 26},
    FISH: {GGP: 25, BAY: 26, MIS: 22, EMB: 8, FIN: 11},
    BAY: {GGP: 22, FISH: 25, MIS: 13, EMB: 19, FIN: 19},
    MIS: {GGP: 17, FISH: 22, BAY: 15, EMB: 19, FIN: 17},
    EMB: {GGP: 25, FISH: 6, BAY: 21, MIS: 20, FIN: 5},
    FIN: {GGP: 23, FISH: 10, BAY: 19, MIS: 17, EMB: 4},
}

# Persons with constraints
persons = [
    {
        "name": "Joseph",
        "location": FISH,
        "avail_start": 8*60,      # 8:00
        "avail_end": 17*60 + 30,  # 17:30
        "min_meet": 90
    },
    {
        "name": "Jeffrey",
        "location": BAY,
        "avail_start": 17*60 + 30, # 17:30
        "avail_end": 21*60 + 30,   # 21:30
        "min_meet": 60
    },
    {
        "name": "Kevin",
        "location": MIS,
        "avail_start": 11*60 + 15, # 11:15
        "avail_end": 15*60 + 15,   # 15:15
        "min_meet": 30
    },
    {
        "name": "David",
        "location": EMB,
        "avail_start": 8*60 + 15,  # 8:15
        "avail_end": 9*60,         # 9:00
        "min_meet": 30
    },
    {
        "name": "Barbara",
        "location": FIN,
        "avail_start": 10*60 + 30, # 10:30
        "avail_end": 16*60 + 30,   # 16:30
        "min_meet": 15
    }
]

index_of = {p["name"]: i for i, p in enumerate(persons)}

# Start info
start_time = 9*60  # 9:00 at Golden Gate Park
start_location = GGP

# Z3 model
opt = Optimize()

n = len(persons)
meet = [Bool(f"meet_{i}") for i in range(n)]
first = [Bool(f"first_{i}") for i in range(n)]
s = [Int(f"s_{i}") for i in range(n)]  # start time
d = [Int(f"d_{i}") for i in range(n)]  # duration
e = [Int(f"e_{i}") for i in range(n)]  # end time = s + d

# Time bounds and availability constraints
for i, p in enumerate(persons):
    opt.add(s[i] >= 0, s[i] <= 1440)
    opt.add(d[i] >= 0, d[i] <= 1440)
    opt.add(e[i] == s[i] + d[i])
    opt.add(e[i] >= 0, e[i] <= 1440)

    # If meeting occurs, it must be within availability window and meet min duration
    opt.add(Implies(meet[i], And(
        s[i] >= p["avail_start"],
        e[i] <= p["avail_end"],
        d[i] >= p["min_meet"]
    )))
    # If not meeting, duration is zero (start time unconstrained beyond bounds)
    opt.add(Implies(Not(meet[i]), d[i] == 0))

# Pairwise ordering with travel times
# b_ij: if true, i happens before j (only meaningful if both are met)
b = {}
for i in range(n):
    for j in range(n):
        if i == j:
            continue
        b[(i, j)] = Bool(f"b_{i}_{j}")
        # Order implies both meetings happen
        opt.add(Implies(b[(i, j)], And(meet[i], meet[j])))

for i in range(n):
    for j in range(i+1, n):
        # If both are met, exactly one must be before the other
        opt.add(Implies(And(meet[i], meet[j]), Or(b[(i, j)], b[(j, i)])))
        opt.add(Not(And(b[(i, j)], b[(j, i)])))
        # Temporal feasibility with travel
        opt.add(Implies(b[(i, j)], s[j] >= e[i] + travel[persons[i]["location"]][persons[j]["location"]]))
        opt.add(Implies(b[(j, i)], s[i] >= e[j] + travel[persons[j]["location"]][persons[i]["location"]]))

# "First meeting" constraints to anchor the chain from the start location/time
any_meet = Bool("any_meet")
opt.add(any_meet == Or(*meet))

sum_first = Sum([If(first[i], 1, 0) for i in range(n)])
opt.add(Implies(any_meet, sum_first == 1))
opt.add(Implies(Not(any_meet), sum_first == 0))

for i, p in enumerate(persons):
    # If someone is first, they must be met and start after traveling from start
    opt.add(Implies(first[i], meet[i]))
    opt.add(Implies(first[i], s[i] >= start_time + travel[start_location][p["location"]]))
    # If person j is first and person k is also met (k != j), then j must be before k
    for k in range(n):
        if k == i:
            continue
        opt.add(Implies(And(first[i], meet[k]), b[(i, k)]))

# Objective 1: maximize number of people met
obj1 = Sum([If(meet[i], 1, 0) for i in range(n)])
opt.maximize(obj1)

# Objective 2: maximize total meeting time
obj2 = Sum(d)
opt.maximize(obj2)

# Solve
if opt.check() != sat:
    # Fallback empty itinerary
    result = {"itinerary": []}
    print(json.dumps(result))
else:
    model = opt.model()
    itinerary = []
    for i, p in enumerate(persons):
        if is_true(model.evaluate(meet[i])):
            si = model.evaluate(s[i]).as_long()
            ei = model.evaluate(e[i]).as_long()
            itinerary.append({
                "action": "meet",
                "location": p["location"],
                "person": p["name"],
                "start_time": minutes_to_hhmm(si),
                "end_time": minutes_to_hhmm(ei)
            })
    # Sort by start time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0])*60 + int(x["start_time"].split(":")[1])))

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))