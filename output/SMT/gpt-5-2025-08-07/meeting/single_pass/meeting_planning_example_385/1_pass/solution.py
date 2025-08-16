# Z3-based solver for the SF friend-meeting itinerary optimization
# Objective: maximize the number of friends whose minimum meeting duration within availability can be met,
# while respecting travel times and start location/time.

from z3 import Optimize, Int, Bool, Sum, If, And, Or, Not, sat
import json

def hm(h, m):
    return h*60 + m

def min_to_hhmm(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Problem data
start_location = "Nob Hill"
start_time = hm(9, 0)  # 09:00

people = [
    {"name": "Jeffrey", "loc": "Presidio", "avail": (hm(8, 0), hm(10, 0)), "min": 105},
    {"name": "Steven", "loc": "North Beach", "avail": (hm(13, 30), hm(22, 0)), "min": 45},
    {"name": "Barbara", "loc": "Fisherman's Wharf", "avail": (hm(18, 0), hm(21, 30)), "min": 30},
    {"name": "John", "loc": "Pacific Heights", "avail": (hm(9, 0), hm(13, 30)), "min": 15},
]

# Travel times in minutes (directed)
travel = {
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "Pacific Heights"): 8,

    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Pacific Heights"): 11,

    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Pacific Heights"): 8,

    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Pacific Heights"): 12,

    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
}

def t(a, b):
    return travel[(a, b)]

# Build Z3 model
opt = Optimize()

n = len(people)
start_vars = []
end_vars = []
sel_vars = []

DAY_END = 24 * 60

for p in people:
    s = Int(f"start_{p['name']}")
    e = Int(f"end_{p['name']}")
    sel = Bool(f"sel_{p['name']}")
    start_vars.append(s)
    end_vars.append(e)
    sel_vars.append(sel)

    # Bounds
    opt.add(s >= 0, s <= DAY_END, e >= 0, e <= DAY_END)

    # If selected: must fit in availability and respect duration
    avail_s, avail_e = p["avail"]
    dur = p["min"]
    opt.add(If(sel, And(s >= avail_s, e <= avail_e, e == s + dur), And(s == 0, e == 0)))

# Pairwise non-overlap + travel constraints
for i in range(n):
    for j in range(i+1, n):
        pi, pj = people[i], people[j]
        si, ei, seli = start_vars[i], end_vars[i], sel_vars[i]
        sj, ej, selj = start_vars[j], end_vars[j], sel_vars[j]
        # If both selected, either i before j with travel, or j before i with travel
        opt.add(If(And(seli, selj),
                   Or(ei + t(pi["loc"], pj["loc"]) <= sj,
                      ej + t(pj["loc"], pi["loc"]) <= si),
                   True))

# Reachability constraints: every scheduled meeting must be reachable from the start
# or from some other scheduled meeting finished earlier with travel time.
for i in range(n):
    p_i = people[i]
    si, ei, seli = start_vars[i], end_vars[i], sel_vars[i]

    preds = []
    # From start location at start_time
    preds.append(start_time + t(start_location, p_i["loc"]) <= si)
    # Or from any other meeting j
    for j in range(n):
        if j == i:
            continue
        p_j = people[j]
        ej, selj = end_vars[j], sel_vars[j]
        preds.append(And(selj, ej + t(p_j["loc"], p_i["loc"]) <= si))
    opt.add(If(seli, Or(*preds), True))

# Objective: maximize number of people met
maximize_count = opt.maximize(Sum([If(sel, 1, 0) for sel in sel_vars]))
# Tie-breaker: push selected meetings as early as possible
opt.minimize(Sum([If(sel_vars[i], start_vars[i], 0) for i in range(n)]))

res = opt.check()
itinerary = []
if res == sat:
    m = opt.model()
    meetings = []
    for i, p in enumerate(people):
        if m.eval(sel_vars[i], model_completion=True):
            s = m.eval(start_vars[i]).as_long()
            e = m.eval(end_vars[i]).as_long()
            meetings.append((s, {
                "action": "meet",
                "person": p["name"],
                "start_time": min_to_hhmm(s),
                "end_time": min_to_hhmm(e)
            }))
    meetings.sort(key=lambda x: x[0])
    itinerary = [entry for _, entry in meetings]

solution = {"itinerary": itinerary}
print(json.dumps(solution, ensure_ascii=False))