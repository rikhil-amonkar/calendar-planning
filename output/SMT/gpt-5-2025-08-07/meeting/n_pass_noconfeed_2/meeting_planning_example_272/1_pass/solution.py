from z3 import *
import json

def minutes(h, m):
    return h*60 + m

# Time windows (minutes from midnight)
availability = {
    1: (minutes(18,30), minutes(21,45)),  # Patricia @ Nob Hill
    2: (minutes(20,30), minutes(21,15)),  # Ashley @ Mission District
    3: (minutes(9,45),  minutes(17,45))   # Timothy @ Embarcadero
}
min_duration = {
    1: 90,   # Patricia
    2: 45,   # Ashley
    3: 120   # Timothy
}
# Person ID -> (Name, Location Name)
person_info = {
    1: ("Patricia", "Nob Hill"),
    2: ("Ashley", "Mission District"),
    3: ("Timothy", "Embarcadero")
}
# Locations
loc_ids = {
    "Russian Hill": 1,
    "Nob Hill": 2,
    "Mission District": 3,
    "Embarcadero": 4
}
# Person -> location id
person_loc = {
    1: loc_ids["Nob Hill"],
    2: loc_ids["Mission District"],
    3: loc_ids["Embarcadero"]
}
# Travel times (directed, in minutes)
t = {}
for a in loc_ids.values():
    t[a] = {b: 0 for b in loc_ids.values()}
t[loc_ids["Russian Hill"]][loc_ids["Nob Hill"]] = 5
t[loc_ids["Russian Hill"]][loc_ids["Mission District"]] = 16
t[loc_ids["Russian Hill"]][loc_ids["Embarcadero"]] = 8
t[loc_ids["Nob Hill"]][loc_ids["Russian Hill"]] = 5
t[loc_ids["Nob Hill"]][loc_ids["Mission District"]] = 13
t[loc_ids["Nob Hill"]][loc_ids["Embarcadero"]] = 9
t[loc_ids["Mission District"]][loc_ids["Russian Hill"]] = 15
t[loc_ids["Mission District"]][loc_ids["Nob Hill"]] = 12
t[loc_ids["Mission District"]][loc_ids["Embarcadero"]] = 19
t[loc_ids["Embarcadero"]][loc_ids["Russian Hill"]] = 8
t[loc_ids["Embarcadero"]][loc_ids["Nob Hill"]] = 10
t[loc_ids["Embarcadero"]][loc_ids["Mission District"]] = 20

day_start_loc = loc_ids["Russian Hill"]
day_start_time = minutes(9,0)

# Z3 Variables
s1, s2, s3 = Ints('s1 s2 s3')  # slot person IDs: 0 none, 1 Patricia, 2 Ashley, 3 Timothy
st1, en1 = Ints('st1 en1')
st2, en2 = Ints('st2 en2')
st3, en3 = Ints('st3 en3')

opt = Optimize()

# Domain constraints
for s in [s1, s2, s3]:
    opt.add(And(s >= 0, s <= 3))
for st, en in [(st1,en1), (st2,en2), (st3,en3)]:
    opt.add(And(st >= 0, st <= 24*60, en >= 0, en <= 24*60, en >= st))

# Enforce slots packed: if later slot used, previous must be used
opt.add(Implies(s2 != 0, s1 != 0))
opt.add(Implies(s3 != 0, s2 != 0))

# No duplicate persons across used slots
opt.add(Or(s1==0, s2==0, s1 != s2))
opt.add(Or(s1==0, s3==0, s1 != s3))
opt.add(Or(s2==0, s3==0, s2 != s3))

# If a slot is empty, force its times to 0 for cleanliness
opt.add(Implies(s1 == 0, And(st1 == 0, en1 == 0)))
opt.add(Implies(s2 == 0, And(st2 == 0, en2 == 0)))
opt.add(Implies(s3 == 0, And(st3 == 0, en3 == 0)))

# Helper to build travel expressions
def travel_from_start_expr(s):
    # s in {0,1,2,3}
    expr = IntVal(0)
    for i in [1,2,3]:
        expr = If(s == i, IntVal(t[day_start_loc][person_loc[i]]), expr)
    return expr

def travel_between_expr(sa, sb):
    expr = IntVal(0)
    for i in [1,2,3]:
        for j in [1,2,3]:
            expr = If(And(sa == i, sb == j), IntVal(t[person_loc[i]][person_loc[j]]), expr)
    return expr

# Meeting constraints per slot
def per_slot_constraints(s, st, en):
    # If assigned to person i, apply availability and minimum duration
    cs = []
    for i in [1,2,3]:
        a_start, a_end = availability[i]
        cs.append(Implies(s == i, And(st >= a_start, en <= a_end, en - st >= min_duration[i])))
    # If empty, already enforced st=en=0
    return cs

for cons in per_slot_constraints(s1, st1, en1): opt.add(cons)
for cons in per_slot_constraints(s2, st2, en2): opt.add(cons)
for cons in per_slot_constraints(s3, st3, en3): opt.add(cons)

# Start-of-day travel to first used slot
opt.add(Implies(s1 != 0, st1 >= day_start_time + travel_from_start_expr(s1)))

# Travel between consecutive slots (only when both used)
opt.add(Implies(And(s1 != 0, s2 != 0), st2 >= en1 + travel_between_expr(s1, s2)))
opt.add(Implies(And(s2 != 0, s3 != 0), st3 >= en2 + travel_between_expr(s2, s3)))

# Objective: maximize number of friends met
used_flags = [Or(s1==i, s2==i, s3==i) for i in [1,2,3]]
meet_count = Sum([If(flag, IntVal(1), IntVal(0)) for flag in used_flags])
opt.maximize(meet_count)

# Secondary objectives: minimize last end time, minimize total travel time
last_end = Int('last_end')
opt.add(last_end == If(s3 != 0, en3, If(s2 != 0, en2, If(s1 != 0, en1, day_start_time))))
opt.minimize(last_end)

total_travel = Int('total_travel')
initial_travel = If(s1 != 0, travel_from_start_expr(s1), IntVal(0))
travel12 = If(And(s1 != 0, s2 != 0), travel_between_expr(s1, s2), IntVal(0))
travel23 = If(And(s2 != 0, s3 != 0), travel_between_expr(s2, s3), IntVal(0))
opt.add(total_travel == initial_travel + travel12 + travel23)
opt.minimize(total_travel)

# Solve
if opt.check() != sat:
    raise RuntimeError("No feasible schedule found.")

m = opt.model()

def val(x):
    return m.evaluate(x).as_long()

# Extract itinerary
slots = [
    (val(s1), val(st1), val(en1)),
    (val(s2), val(st2), val(en2)),
    (val(s3), val(st3), val(en3))
]

def fmt_time(mins):
    h = mins // 60
    mm = mins % 60
    return f"{h}:{mm:02d}"

itinerary = []
for pid, st, en in slots:
    if pid == 0:
        continue
    person, location = person_info[pid]
    itinerary.append({
        "action": "meet",
        "location": location,
        "person": person,
        "start_time": fmt_time(st),
        "end_time": fmt_time(en)
    })

output = {"itinerary": itinerary}
print(json.dumps(output, ensure_ascii=False))