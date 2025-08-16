# Requires: z3-solver (pip install z3-solver)
from z3 import Optimize, Int, Bool, And, Or, Not, If, Sum
import json

def minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def m2str(m):
    h = m // 60
    mins = m % 60
    return f"{h:02d}:{mins:02d}"

# Locations
W = "Fisherman's Wharf"
G = "Golden Gate Park"
P = "Presidio"
R = "Richmond District"

# Travel times (minutes), directional as given
t = {
    (W, G): 25, (W, P): 17, (W, R): 18,
    (G, W): 24, (G, P): 11, (G, R): 7,
    (P, W): 19, (P, G): 12, (P, R): 7,
    (R, W): 18, (R, G): 9, (R, P): 7,
}

def dist(a, b):
    return t[(a, b)]

start_time = minutes("09:00")
start_loc = W

# Friends data: name -> (location, available_start, available_end, min_duration)
friends = {
    "Melissa": (G, minutes("08:30"), minutes("20:00"), 15),
    "Nancy":   (P, minutes("19:45"), minutes("22:00"), 105),
    "Emily":   (R, minutes("16:45"), minutes("22:00"), 120),
}
names = list(friends.keys())

# Z3 variables
s = {n: Int(f"s_{n}") for n in names}
e = {n: Int(f"e_{n}") for n in names}
a = {n: Int(f"a_{n}") for n in names}  # 0/1 attendance

# Precedence/order booleans for travel feasibility between meetings
order = {}
for i in range(len(names)):
    for j in range(len(names)):
        if i == j:
            continue
        ni, nj = names[i], names[j]
        order[(ni, nj)] = Bool(f"order_{ni}_before_{nj}")

opt = Optimize()
opt.set(priority='lex')  # maximize attendees, then minimize time/delay preferences

# Constraints per friend
for n in names:
    loc, avail_s, avail_e, min_d = friends[n]
    opt.add(a[n] >= 0, a[n] <= 1)
    opt.add(s[n] >= 0, e[n] >= 0)
    opt.add(e[n] >= s[n])
    # Duration if attended
    opt.add(e[n] - s[n] >= min_d * a[n])
    # Availability if attended
    opt.add(If(a[n] == 1, s[n] >= avail_s, True))
    opt.add(If(a[n] == 1, e[n] <= avail_e, True))

# Travel feasibility between attended meetings via disjunction with order variables
for i in range(len(names)):
    for j in range(i + 1, len(names)):
        ni, nj = names[i], names[j]
        li, lj = friends[ni][0], friends[nj][0]
        tij = dist(li, lj)
        tji = dist(lj, li)
        # If both attended and ni before nj, enforce travel from ni to nj
        opt.add(Implies(And(a[ni] == 1, a[nj] == 1, order[(ni, nj)]), e[ni] + tij <= s[nj]))
        # If both attended and nj before ni, enforce travel from nj to ni
        opt.add(Implies(And(a[ni] == 1, a[nj] == 1, Not(order[(ni, nj)])), e[nj] + tji <= s[ni]))
        # Note: order[(ni, nj)] and its negation are only relevant when both are attended.

# Anchor the first attended meeting to the trip start at Fisherman's Wharf
for n in names:
    loc, _, _, _ = friends[n]
    has_prev = Or([And(a[m] == 1, order[(m, n)]) for m in names if m != n] or [False])
    opt.add(Implies(And(a[n] == 1, Not(has_prev)), s[n] >= start_time + dist(start_loc, loc)))

# Objective 1: maximize number of friends met
opt.maximize(Sum([a[n] for n in names]))
# Objective 2: minimize total meeting time used (prefer minimum necessary)
opt.minimize(Sum([If(a[n] == 1, e[n] - s[n], 0) for n in names]))
# Objective 3: minimize sum of start times (prefer earlier meetings)
opt.minimize(Sum([If(a[n] == 1, s[n], 0) for n in names]))

res = opt.check()
if str(res) != "sat":
    print(json.dumps({"itinerary": []}, indent=2))
    raise SystemExit(0)

m = opt.model()

meetings = []
for n in names:
    if m[a[n]].as_long() == 1:
        start = m[s[n]].as_long()
        end = m[e[n]].as_long()
        meetings.append({
            "action": "meet",
            "person": n,
            "start_time": m2str(start),
            "end_time": m2str(end),
        })

# Sort by start time
meetings.sort(key=lambda x: x["start_time"])

print(json.dumps({"itinerary": meetings}, indent=2))