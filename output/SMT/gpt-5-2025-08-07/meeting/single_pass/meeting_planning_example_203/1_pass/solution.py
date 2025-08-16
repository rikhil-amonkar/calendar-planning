# Solve the SF day-meetings problem using Z3 Optimize

from z3 import *
import json

def minutes(h, m):
    return h * 60 + m

def fmt_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

# Locations
FD = "FD"
FW = "FW"
PH = "PH"
MD = "MD"

# Directed travel times (minutes)
travel = {
    (FD, FW): 10, (FD, PH): 13, (FD, MD): 17,
    (FW, FD): 11, (FW, PH): 12, (FW, MD): 22,
    (PH, FD): 13, (PH, FW): 13, (PH, MD): 15,
    (MD, FD): 17, (MD, FW): 22, (MD, PH): 16,
}
# zero for same-location transitions
for a in [FD, FW, PH, MD]:
    travel[(a, a)] = 0

# People and constraints
people = [
    {"name": "David",   "loc": FW, "avail": (minutes(10,45), minutes(15,30)), "min_dur": 15},
    {"name": "Timothy", "loc": PH, "avail": (minutes(9,0),  minutes(15,30)), "min_dur": 75},
    {"name": "Robert",  "loc": MD, "avail": (minutes(12,15), minutes(19,45)), "min_dur": 90},
]

# Anchor start at Financial District at 09:00
anchor = {"name": "_START", "loc": FD, "avail": (minutes(9,0), minutes(9,0)), "min_dur": 0}

# Horizon bounds
H_START = minutes(9, 0)
H_END   = minutes(20, 0)

opt = Optimize()
opt.set(priority='lex')  # maximize count, then minimize finish time, then minimize total meeting duration

# Variables per person
vars_by_name = {}
for p in people:
    s = Int(f"s_{p['name']}")
    e = Int(f"e_{p['name']}")
    meet = Bool(f"meet_{p['name']}")
    vars_by_name[p['name']] = (s, e, meet)

    # Bounds
    opt.add(s >= H_START, s <= H_END)
    opt.add(e >= H_START, e <= H_END)
    opt.add(e >= s)

    # If meeting, respect availability and min duration
    a0, a1 = p["avail"]
    min_d = p["min_dur"]
    opt.add(Implies(meet, And(s >= a0, e <= a1, e - s >= min_d)))
    # If not meeting, duration can be zero (allow s == e anywhere in horizon)
    opt.add(Implies(Not(meet), e == s))

# Anchor fixed variables
sA = Int("s__START")
eA = Int("e__START")
opt.add(sA == anchor["avail"][0], eA == anchor["avail"][1])  # both 09:00

# Disjunctive travel/order constraints
# Between anchor and each person: if person is met, they must be after anchor (or infeasible otherwise)
for p in people:
    s, e, meet = vars_by_name[p["name"]]
    oA = Bool(f"ord__START_{p['name']}")  # True if anchor before p
    # If met and anchor before p: arrive via travel from FD
    opt.add(Implies(And(meet, oA), s >= eA + travel[(anchor["loc"], p["loc"])]))
    # If met and p before anchor: return to FD before 09:00 (will be infeasible; solver will choose oA True)
    opt.add(Implies(And(meet, Not(oA)), e + travel[(p["loc"], anchor["loc"])] <= sA))

# Between all pairs of people, if both met, enforce one before the other with travel time
for i in range(len(people)):
    for j in range(i+1, len(people)):
        pi = people[i]
        pj = people[j]
        si, ei, mi = vars_by_name[pi["name"]]
        sj, ej, mj = vars_by_name[pj["name"]]
        oij = Bool(f"ord_{pi['name']}_{pj['name']}")  # True if i before j
        opt.add(Implies(And(mi, mj, oij), sj >= ei + travel[(pi["loc"], pj["loc"])]))
        opt.add(Implies(And(mi, mj, Not(oij)), si >= ej + travel[(pj["loc"], pi["loc"])]))

# Objective 1: maximize number of friends met
count = Sum([If(vars_by_name[p["name"]][2], 1, 0) for p in people])
opt.maximize(count)

# Objective 2: minimize end time of last meeting
last_end = Int("last_end")
opt.add(last_end >= H_START, last_end <= H_END)
for p in people:
    s, e, meet = vars_by_name[p["name"]]
    opt.add(Implies(meet, last_end >= e))
opt.minimize(last_end)

# Objective 3: minimize total meeting duration (drives to minimum required durations)
total_meet_time = Sum([If(vars_by_name[p["name"]][2], vars_by_name[p["name"]][1] - vars_by_name[p["name"]][0], 0) for p in people])
opt.minimize(total_meet_time)

# Solve
if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()
    meetings = []
    for p in people:
        s, e, meet = vars_by_name[p["name"]]
        if is_true(m[meet]):
            s_val = m[s].as_long()
            e_val = m[e].as_long()
            meetings.append({
                "action": "meet",
                "person": p["name"],
                "start_time": fmt_time(s_val),
                "end_time": fmt_time(e_val),
            })
    # Sort by start time
    meetings.sort(key=lambda x: x["start_time"])
    print(json.dumps({"itinerary": meetings}))