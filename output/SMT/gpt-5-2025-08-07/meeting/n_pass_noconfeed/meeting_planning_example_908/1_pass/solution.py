import json
from z3 import *

def parse_time(s):
    s = s.strip().upper()
    # Format like '8:15AM' or '3:00PM'
    am = 'AM' in s
    pm = 'PM' in s
    s = s.replace('AM', '').replace('PM', '').strip()
    h, m = s.split(':')
    h = int(h)
    m = int(m)
    if pm and h != 12:
        h += 12
    if am and h == 12:
        h = 0
    return h * 60 + m

def fmt_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

# Travel times (minutes), directed
travel = {
    ("Financial District","Fisherman's Wharf"): 10,
    ("Financial District","Presidio"): 22,
    ("Financial District","Bayview"): 19,
    ("Financial District","Haight-Ashbury"): 19,
    ("Financial District","Russian Hill"): 11,
    ("Financial District","The Castro"): 20,
    ("Financial District","Marina District"): 15,
    ("Financial District","Richmond District"): 21,
    ("Financial District","Union Square"): 9,
    ("Financial District","Sunset District"): 30,

    ("Fisherman's Wharf","Financial District"): 11,
    ("Fisherman's Wharf","Presidio"): 17,
    ("Fisherman's Wharf","Bayview"): 26,
    ("Fisherman's Wharf","Haight-Ashbury"): 22,
    ("Fisherman's Wharf","Russian Hill"): 7,
    ("Fisherman's Wharf","The Castro"): 27,
    ("Fisherman's Wharf","Marina District"): 9,
    ("Fisherman's Wharf","Richmond District"): 18,
    ("Fisherman's Wharf","Union Square"): 13,
    ("Fisherman's Wharf","Sunset District"): 27,

    ("Presidio","Financial District"): 23,
    ("Presidio","Fisherman's Wharf"): 19,
    ("Presidio","Bayview"): 31,
    ("Presidio","Haight-Ashbury"): 15,
    ("Presidio","Russian Hill"): 14,
    ("Presidio","The Castro"): 21,
    ("Presidio","Marina District"): 11,
    ("Presidio","Richmond District"): 7,
    ("Presidio","Union Square"): 22,
    ("Presidio","Sunset District"): 15,

    ("Bayview","Financial District"): 19,
    ("Bayview","Fisherman's Wharf"): 25,
    ("Bayview","Presidio"): 32,
    ("Bayview","Haight-Ashbury"): 19,
    ("Bayview","Russian Hill"): 23,
    ("Bayview","The Castro"): 19,
    ("Bayview","Marina District"): 27,
    ("Bayview","Richmond District"): 25,
    ("Bayview","Union Square"): 18,
    ("Bayview","Sunset District"): 23,

    ("Haight-Ashbury","Financial District"): 21,
    ("Haight-Ashbury","Fisherman's Wharf"): 23,
    ("Haight-Ashbury","Presidio"): 15,
    ("Haight-Ashbury","Bayview"): 18,
    ("Haight-Ashbury","Russian Hill"): 17,
    ("Haight-Ashbury","The Castro"): 6,
    ("Haight-Ashbury","Marina District"): 17,
    ("Haight-Ashbury","Richmond District"): 10,
    ("Haight-Ashbury","Union Square"): 19,
    ("Haight-Ashbury","Sunset District"): 15,

    ("Russian Hill","Financial District"): 11,
    ("Russian Hill","Fisherman's Wharf"): 7,
    ("Russian Hill","Presidio"): 14,
    ("Russian Hill","Bayview"): 23,
    ("Russian Hill","Haight-Ashbury"): 17,
    ("Russian Hill","The Castro"): 21,
    ("Russian Hill","Marina District"): 7,
    ("Russian Hill","Richmond District"): 14,
    ("Russian Hill","Union Square"): 10,
    ("Russian Hill","Sunset District"): 23,

    ("The Castro","Financial District"): 21,
    ("The Castro","Fisherman's Wharf"): 24,
    ("The Castro","Presidio"): 20,
    ("The Castro","Bayview"): 19,
    ("The Castro","Haight-Ashbury"): 6,
    ("The Castro","Russian Hill"): 18,
    ("The Castro","Marina District"): 21,
    ("The Castro","Richmond District"): 16,
    ("The Castro","Union Square"): 19,
    ("The Castro","Sunset District"): 17,

    ("Marina District","Financial District"): 17,
    ("Marina District","Fisherman's Wharf"): 10,
    ("Marina District","Presidio"): 10,
    ("Marina District","Bayview"): 27,
    ("Marina District","Haight-Ashbury"): 16,
    ("Marina District","Russian Hill"): 8,
    ("Marina District","The Castro"): 22,
    ("Marina District","Richmond District"): 11,
    ("Marina District","Union Square"): 16,
    ("Marina District","Sunset District"): 19,

    ("Richmond District","Financial District"): 22,
    ("Richmond District","Fisherman's Wharf"): 18,
    ("Richmond District","Presidio"): 7,
    ("Richmond District","Bayview"): 27,
    ("Richmond District","Haight-Ashbury"): 10,
    ("Richmond District","Russian Hill"): 13,
    ("Richmond District","The Castro"): 16,
    ("Richmond District","Marina District"): 9,
    ("Richmond District","Union Square"): 21,
    ("Richmond District","Sunset District"): 11,

    ("Union Square","Financial District"): 9,
    ("Union Square","Fisherman's Wharf"): 15,
    ("Union Square","Presidio"): 24,
    ("Union Square","Bayview"): 15,
    ("Union Square","Haight-Ashbury"): 18,
    ("Union Square","Russian Hill"): 13,
    ("Union Square","The Castro"): 17,
    ("Union Square","Marina District"): 18,
    ("Union Square","Richmond District"): 20,
    ("Union Square","Sunset District"): 27,

    ("Sunset District","Financial District"): 30,
    ("Sunset District","Fisherman's Wharf"): 29,
    ("Sunset District","Presidio"): 16,
    ("Sunset District","Bayview"): 22,
    ("Sunset District","Haight-Ashbury"): 15,
    ("Sunset District","Russian Hill"): 24,
    ("Sunset District","The Castro"): 17,
    ("Sunset District","Marina District"): 21,
    ("Sunset District","Richmond District"): 12,
    ("Sunset District","Union Square"): 30,
}

day_start_loc = "Financial District"
day_start_time = parse_time("9:00AM")

# People and constraints
people = [
    {"person":"Mark", "location":"Fisherman's Wharf", "start":parse_time("8:15AM"), "end":parse_time("10:00AM"), "min":30},
    {"person":"Stephanie", "location":"Presidio", "start":parse_time("12:15PM"), "end":parse_time("3:00PM"), "min":75},
    {"person":"Betty", "location":"Bayview", "start":parse_time("7:15AM"), "end":parse_time("8:30PM"), "min":15},
    {"person":"Lisa", "location":"Haight-Ashbury", "start":parse_time("3:30PM"), "end":parse_time("6:30PM"), "min":45},
    {"person":"William", "location":"Russian Hill", "start":parse_time("6:45PM"), "end":parse_time("8:00PM"), "min":60},
    {"person":"Brian", "location":"The Castro", "start":parse_time("9:15AM"), "end":parse_time("1:15PM"), "min":30},
    {"person":"Joseph", "location":"Marina District", "start":parse_time("10:45AM"), "end":parse_time("3:00PM"), "min":90},
    {"person":"Ashley", "location":"Richmond District", "start":parse_time("9:45AM"), "end":parse_time("11:15AM"), "min":45},
    {"person":"Patricia", "location":"Union Square", "start":parse_time("4:30PM"), "end":parse_time("8:00PM"), "min":120},
    {"person":"Karen", "location":"Sunset District", "start":parse_time("4:30PM"), "end":parse_time("10:00PM"), "min":105},
]

n = len(people)

# Z3 variables
start_vars = {p['person']: Int(f"start_{i}") for i,p in enumerate(people)}
end_vars   = {p['person']: Int(f"end_{i}")   for i,p in enumerate(people)}
dur_vars   = {p['person']: Int(f"dur_{i}")   for i,p in enumerate(people)}
pos_vars   = {p['person']: Int(f"pos_{i}")   for i,p in enumerate(people)}
attend_vars= {p['person']: Bool(f"attend_{i}") for i,p in enumerate(people)}
pred_start = {p['person']: Bool(f"predStart_{i}") for i,p in enumerate(people)}
# predecessor booleans pred_ij: i is predecessor of j
pred_ij = {}
for j, pj in enumerate(people):
    for i, pi in enumerate(people):
        if i == j: 
            continue
        pred_ij[(pi['person'], pj['person'])] = Bool(f"pred_{i}_to_{j}")

opt = Optimize()

# Basic meeting window and duration constraints
for i, p in enumerate(people):
    name = p['person']
    ws = p['start']
    we = p['end']
    mmin = p['min']
    s = start_vars[name]
    e = end_vars[name]
    d = dur_vars[name]
    pos = pos_vars[name]
    attend = attend_vars[name]

    opt.add(Implies(attend, And(s >= ws, e <= we, d >= mmin, e == s + d)))
    opt.add(Implies(Not(attend), And(d == 0, pos == -1)))

    # Bound times reasonably within the day
    opt.add(s >= 0, e >= 0, d >= 0)

    # Position domain: either -1 if not attending, else in [0, n-1]
    opt.add(Implies(attend, And(pos >= 0, pos < n)))
    opt.add(Implies(Not(attend), pos == -1))

# Distinct positions among attended meetings
for a in range(n):
    for b in range(a+1, n):
        na = people[a]['person']
        nb = people[b]['person']
        opt.add(Implies(And(attend_vars[na], attend_vars[nb]), pos_vars[na] != pos_vars[nb]))

# Predecessor structure constraints
# For each meeting j: exactly one predecessor (either start sentinel or some i), if attending.
for j, pj in enumerate(people):
    name_j = pj['person']
    loc_j = pj['location']

    preds = [pred_ij[(people[i]['person'], name_j)] for i in range(n) if i != j]
    sum_preds = Sum([If(b, 1, 0) for b in preds] + [If(pred_start[name_j], 1, 0)])
    attend_j = attend_vars[name_j]
    opt.add(Implies(attend_j, sum_preds == 1))
    opt.add(Implies(Not(attend_j), sum_preds == 0))

    # If start sentinel is predecessor, enforce it's the first and reachable from day start
    # Ensure travel time from starting location
    t_from_start = travel[(day_start_loc, loc_j)]
    opt.add(Implies(pred_start[name_j],
                    And(attend_j,
                        pos_vars[name_j] == 0,
                        start_vars[name_j] >= day_start_time + t_from_start)))

    # If some i is predecessor of j, enforce adjacency and travel timing
    for i, pi in enumerate(people):
        if i == j:
            continue
        name_i = pi['person']
        loc_i = pi['location']
        b = pred_ij[(name_i, name_j)]
        t_ij = travel[(loc_i, loc_j)]
        opt.add(Implies(b, And(attend_vars[name_i],
                               attend_j,
                               pos_vars[name_j] == pos_vars[name_i] + 1,
                               start_vars[name_j] >= end_vars[name_i] + t_ij)))

# Exactly one start sentinel if any meeting is attended
any_attend = Or([attend_vars[p['person']] for p in people])
opt.add(Implies(Not(any_attend), Sum([If(pred_start[p['person']], 1, 0) for p in people]) == 0))
opt.add(Implies(any_attend, Sum([If(pred_start[p['person']], 1, 0) for p in people]) == 1))

# Objective: maximize number of meetings, then maximize total meeting time
total_meetings = Sum([If(attend_vars[p['person']], 1, 0) for p in people])
total_duration = Sum([dur_vars[p['person']] for p in people])
opt.maximize(total_meetings)
opt.maximize(total_duration)

# Solve
if opt.check() != sat:
    # If unsat, output empty itinerary
    print(json.dumps({"itinerary": []}, indent=2))
    exit(0)

m = opt.model()

# Build itinerary ordered by position
attended = []
for p in people:
    name = p['person']
    if is_true(m.evaluate(attend_vars[name])):
        pos = m.evaluate(pos_vars[name]).as_long()
        s = m.evaluate(start_vars[name]).as_long()
        e = m.evaluate(end_vars[name]).as_long()
        attended.append((pos, p['location'], name, s, e))

attended.sort(key=lambda x: x[0])

itinerary = []
for pos, loc, person, s, e in attended:
    itinerary.append({
        "action": "meet",
        "location": loc,
        "person": person,
        "start_time": fmt_time(s),
        "end_time": fmt_time(e)
    })

print(json.dumps({"itinerary": itinerary}, indent=2))