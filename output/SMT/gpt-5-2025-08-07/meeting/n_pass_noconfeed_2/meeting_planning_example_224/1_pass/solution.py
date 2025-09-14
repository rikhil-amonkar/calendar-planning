from z3 import *
import json

def minutes(h, m):
    return h*60 + m

def fmt_time(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h}:{m:02d}"

# Data
start_location = "Fisherman's Wharf"
start_time = minutes(9, 0)  # 9:00

persons = {
    1: "Melissa",
    2: "Nancy",
    3: "Emily"
}

person_location = {
    1: "Golden Gate Park",
    2: "Presidio",
    3: "Richmond District"
}

# Availability windows (start, end) in minutes
availability = {
    1: (minutes(8, 30), minutes(20, 0)),   # Melissa
    2: (minutes(19, 45), minutes(22, 0)),  # Nancy
    3: (minutes(16, 45), minutes(22, 0))   # Emily
}

# Minimum meeting durations
min_duration = {
    1: 15,    # Melissa
    2: 105,   # Nancy
    3: 120    # Emily
}

# Travel times (directed) in minutes
travel = {
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18,

    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Richmond District"): 7,

    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Richmond District"): 7,

    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Presidio"): 7,
}

# Helper to select integer by person Int var
def select_by_person(pvar, mapping, default=0):
    expr = IntVal(default)
    for pid in sorted(mapping.keys()):
        expr = If(pvar == pid, IntVal(mapping[pid]), expr)
    return expr

# Helper to select travel from starting location to person
def travel_start_to_person(pvar):
    m = {
        1: travel[(start_location, person_location[1])],
        2: travel[(start_location, person_location[2])],
        3: travel[(start_location, person_location[3])]
    }
    return select_by_person(pvar, m, default=0)

# Helper to select travel between two person locations
def travel_between_persons(pprev, pcur):
    expr = IntVal(0)
    pairs = [
        (1, 2, travel[(person_location[1], person_location[2])]),
        (1, 3, travel[(person_location[1], person_location[3])]),
        (2, 1, travel[(person_location[2], person_location[1])]),
        (2, 3, travel[(person_location[2], person_location[3])]),
        (3, 1, travel[(person_location[3], person_location[1])]),
        (3, 2, travel[(person_location[3], person_location[2])]),
    ]
    for a, b, val in pairs:
        expr = If(And(pprev == a, pcur == b), IntVal(val), expr)
    return expr

# Build SMT model
opt = Optimize()

num_slots = 3  # up to number of friends
person_slot = [Int(f"person_{i}") for i in range(num_slots)]
used = [Bool(f"used_{i}") for i in range(num_slots)]
start_vars = [Int(f"start_{i}") for i in range(num_slots)]
end_vars = [Int(f"end_{i}") for i in range(num_slots)]

# Domains
for i in range(num_slots):
    opt.add(person_slot[i] >= 0, person_slot[i] <= 3)
    opt.add(used[i] == (person_slot[i] != 0))
    opt.add(start_vars[i] >= 0, start_vars[i] <= 24*60)
    opt.add(end_vars[i] >= 0, end_vars[i] <= 24*60)
    opt.add(end_vars[i] >= start_vars[i])

# Nonincreasing used: if slot i is used, then slot i-1 is used
for i in range(1, num_slots):
    opt.add(Or(Not(used[i]), used[i-1]))

# No duplicate persons across slots (ignoring zeros)
for i in range(num_slots):
    for j in range(i+1, num_slots):
        opt.add(Or(person_slot[i] == 0, person_slot[j] == 0, person_slot[i] != person_slot[j]))

# Availability and minimum duration constraints
for i in range(num_slots):
    avail_start_expr = If(
        person_slot[i] == 1, IntVal(availability[1][0]),
        If(person_slot[i] == 2, IntVal(availability[2][0]),
           If(person_slot[i] == 3, IntVal(availability[3][0]), IntVal(0)))
    )
    avail_end_expr = If(
        person_slot[i] == 1, IntVal(availability[1][1]),
        If(person_slot[i] == 2, IntVal(availability[2][1]),
           If(person_slot[i] == 3, IntVal(availability[3][1]), IntVal(24*60)))
    )
    req_expr = If(
        person_slot[i] == 1, IntVal(min_duration[1]),
        If(person_slot[i] == 2, IntVal(min_duration[2]),
           If(person_slot[i] == 3, IntVal(min_duration[3]), IntVal(0)))
    )

    opt.add(Or(Not(used[i]), start_vars[i] >= avail_start_expr))
    opt.add(Or(Not(used[i]), end_vars[i] <= avail_end_expr))
    opt.add(Or(Not(used[i]), end_vars[i] - start_vars[i] >= req_expr))

# Travel time sequencing constraints
# From start to first used slot
opt.add(Or(Not(used[0]), start_vars[0] >= start_time + travel_start_to_person(person_slot[0])))

# Between consecutive used slots
for i in range(1, num_slots):
    travel_expr = travel_between_persons(person_slot[i-1], person_slot[i])
    opt.add(Or(Not(used[i]), start_vars[i] >= end_vars[i-1] + travel_expr))

# Objective: maximize number of meetings, then minimize finish time, then minimize total travel
meet_count = Sum([If(used[i], IntVal(1), IntVal(0)) for i in range(num_slots)])

finish_time = If(used[2], end_vars[2],
                 If(used[1], end_vars[1],
                    If(used[0], end_vars[0], IntVal(start_time))))

t0 = If(used[0], travel_start_to_person(person_slot[0]), IntVal(0))
t1 = If(And(used[0], used[1]), travel_between_persons(person_slot[0], person_slot[1]), IntVal(0))
t2 = If(And(used[1], used[2]), travel_between_persons(person_slot[1], person_slot[2]), IntVal(0))
total_travel = t0 + t1 + t2

opt.maximize(meet_count)
opt.minimize(finish_time)
opt.minimize(total_travel)

if opt.check() != sat:
    # If unsat, output empty itinerary
    print(json.dumps({"itinerary": []}, ensure_ascii=False))
else:
    model = opt.model()
    itinerary = []
    for i in range(num_slots):
        if is_true(model.evaluate(used[i])):
            pid = model.evaluate(person_slot[i]).as_long()
            st = model.evaluate(start_vars[i]).as_long()
            en = model.evaluate(end_vars[i]).as_long()
            entry = {
                "action": "meet",
                "location": person_location[pid],
                "person": persons[pid],
                "start_time": fmt_time(st),
                "end_time": fmt_time(en)
            }
            itinerary.append(entry)
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))