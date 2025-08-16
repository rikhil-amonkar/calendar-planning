# Requires: z3-solver
# pip install z3-solver

from z3 import Optimize, Int, Bool, If, And, Or, Not, Implies
import json

# Time helpers
def to_min(h, m): return h*60 + m
def to_hhmm(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Problem data
start_location = "Bayview"
arrival_time = to_min(9, 0)

people = {
    "Jessica": {
        "location": "Embarcadero",
        "window_start": to_min(16, 45),
        "window_end": to_min(19, 0),
        "min_duration": 30
    },
    "Sandra": {
        "location": "Richmond District",
        "window_start": to_min(18, 30),
        "window_end": to_min(21, 45),
        "min_duration": 120
    },
    "Jason": {
        "location": "Fisherman's Wharf",
        "window_start": to_min(16, 0),
        "window_end": to_min(16, 45),
        "min_duration": 30
    }
}

# Directed travel times (minutes)
T = {
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Fisherman's Wharf"): 25,

    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,

    ("Richmond District", "Bayview"): 26,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Fisherman's Wharf"): 18,

    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Richmond District"): 18,
}

# Z3 model
opt = Optimize()

vars_s = {}
vars_e = {}
vars_attend = {}

for p, info in people.items():
    s = Int(f"s_{p}")
    e = Int(f"e_{p}")
    a = Bool(f"attend_{p}")
    vars_s[p] = s
    vars_e[p] = e
    vars_attend[p] = a

    # Domain bounds
    opt.add(s >= 0, e >= 0, s <= 24*60, e <= 24*60)

    # Attendance constraints
    ws, we, md = info["window_start"], info["window_end"], info["min_duration"]
    opt.add(Or(
        Not(a),
        And(s >= ws, e <= we, e - s >= md, e > s)
    ))

    # Start-of-day lower bound (weak, but safe)
    t0 = T[(start_location, info["location"])]
    opt.add(Or(Not(a), s >= arrival_time + t0))

# Pairwise ordering and travel feasibility
people_list = list(people.keys())
for i in range(len(people_list)):
    for j in range(i+1, len(people_list)):
        p = people_list[i]
        q = people_list[j]
        op = Bool(f"order_{p}_before_{q}")  # True => p before q; False => q before p

        loc_p = people[p]["location"]
        loc_q = people[q]["location"]

        # If both attended, enforce one precedes the other with travel time
        opt.add(Implies(And(vars_attend[p], vars_attend[q], op),
                        vars_e[p] + T[(loc_p, loc_q)] <= vars_s[q]))
        opt.add(Implies(And(vars_attend[p], vars_attend[q], Not(op)),
                        vars_e[q] + T[(loc_q, loc_p)] <= vars_s[p]))

# Objective: maximize number of friends met
meet_count = sum([If(vars_attend[p], 1, 0) for p in people_list])
opt.maximize(meet_count)

# Solve
if opt.check().r == 1:
    m = opt.model()
    meetings = []
    for p in people_list:
        if m.evaluate(vars_attend[p]):
            s = m.evaluate(vars_s[p]).as_long()
            e = m.evaluate(vars_e[p]).as_long()
            meetings.append({
                "action": "meet",
                "person": p,
                "start": s,
                "end": e
            })
    # Sort chronologically
    meetings.sort(key=lambda x: x["start"])
    itinerary = []
    for mt in meetings:
        itinerary.append({
            "action": "meet",
            "person": mt["person"],
            "start_time": to_hhmm(mt["start"]),
            "end_time": to_hhmm(mt["end"])
        })
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))