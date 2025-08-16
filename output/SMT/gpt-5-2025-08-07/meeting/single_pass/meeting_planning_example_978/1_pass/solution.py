# Z3-based scheduler for maximizing number of friend meetings with travel and time-window constraints.

from z3 import Optimize, Int, Bool, BoolVal, If, And, Or, Not, Implies, Sum
import json

def hm_to_min(h, m):
    return h * 60 + m

def min_to_hhmm(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Locations
locs = [
    "Embarcadero",
    "Fisherman's Wharf",
    "Financial District",
    "Russian Hill",
    "Marina District",
    "Richmond District",
    "Pacific Heights",
    "Haight-Ashbury",
    "Presidio",
    "Nob Hill",
    "The Castro",
]

# Directed travel time matrix (minutes) as given
T = {l: {} for l in locs}

# Embarcadero outgoing
T["Embarcadero"]["Fisherman's Wharf"] = 6
T["Embarcadero"]["Financial District"] = 5
T["Embarcadero"]["Russian Hill"] = 8
T["Embarcadero"]["Marina District"] = 12
T["Embarcadero"]["Richmond District"] = 21
T["Embarcadero"]["Pacific Heights"] = 11
T["Embarcadero"]["Haight-Ashbury"] = 21
T["Embarcadero"]["Presidio"] = 20
T["Embarcadero"]["Nob Hill"] = 10
T["Embarcadero"]["The Castro"] = 25

# Fisherman's Wharf outgoing
T["Fisherman's Wharf"]["Embarcadero"] = 8
T["Fisherman's Wharf"]["Financial District"] = 11
T["Fisherman's Wharf"]["Russian Hill"] = 7
T["Fisherman's Wharf"]["Marina District"] = 9
T["Fisherman's Wharf"]["Richmond District"] = 18
T["Fisherman's Wharf"]["Pacific Heights"] = 12
T["Fisherman's Wharf"]["Haight-Ashbury"] = 22
T["Fisherman's Wharf"]["Presidio"] = 17
T["Fisherman's Wharf"]["Nob Hill"] = 11
T["Fisherman's Wharf"]["The Castro"] = 27

# Financial District outgoing
T["Financial District"]["Embarcadero"] = 4
T["Financial District"]["Fisherman's Wharf"] = 10
T["Financial District"]["Russian Hill"] = 11
T["Financial District"]["Marina District"] = 15
T["Financial District"]["Richmond District"] = 21
T["Financial District"]["Pacific Heights"] = 13
T["Financial District"]["Haight-Ashbury"] = 19
T["Financial District"]["Presidio"] = 22
T["Financial District"]["Nob Hill"] = 8
T["Financial District"]["The Castro"] = 20

# Russian Hill outgoing
T["Russian Hill"]["Embarcadero"] = 8
T["Russian Hill"]["Fisherman's Wharf"] = 7
T["Russian Hill"]["Financial District"] = 11
T["Russian Hill"]["Marina District"] = 7
T["Russian Hill"]["Richmond District"] = 14
T["Russian Hill"]["Pacific Heights"] = 7
T["Russian Hill"]["Haight-Ashbury"] = 17
T["Russian Hill"]["Presidio"] = 14
T["Russian Hill"]["Nob Hill"] = 5
T["Russian Hill"]["The Castro"] = 21

# Marina District outgoing
T["Marina District"]["Embarcadero"] = 14
T["Marina District"]["Fisherman's Wharf"] = 10
T["Marina District"]["Financial District"] = 17
T["Marina District"]["Russian Hill"] = 8
T["Marina District"]["Richmond District"] = 11
T["Marina District"]["Pacific Heights"] = 7
T["Marina District"]["Haight-Ashbury"] = 16
T["Marina District"]["Presidio"] = 10
T["Marina District"]["Nob Hill"] = 12
T["Marina District"]["The Castro"] = 22

# Richmond District outgoing
T["Richmond District"]["Embarcadero"] = 19
T["Richmond District"]["Fisherman's Wharf"] = 18
T["Richmond District"]["Financial District"] = 22
T["Richmond District"]["Russian Hill"] = 13
T["Richmond District"]["Marina District"] = 9
T["Richmond District"]["Pacific Heights"] = 10
T["Richmond District"]["Haight-Ashbury"] = 10
T["Richmond District"]["Presidio"] = 7
T["Richmond District"]["Nob Hill"] = 17
T["Richmond District"]["The Castro"] = 16

# Pacific Heights outgoing
T["Pacific Heights"]["Embarcadero"] = 10
T["Pacific Heights"]["Fisherman's Wharf"] = 13
T["Pacific Heights"]["Financial District"] = 13
T["Pacific Heights"]["Russian Hill"] = 7
T["Pacific Heights"]["Marina District"] = 6
T["Pacific Heights"]["Richmond District"] = 12
T["Pacific Heights"]["Haight-Ashbury"] = 11
T["Pacific Heights"]["Presidio"] = 11
T["Pacific Heights"]["Nob Hill"] = 8
T["Pacific Heights"]["The Castro"] = 16

# Haight-Ashbury outgoing
T["Haight-Ashbury"]["Embarcadero"] = 20
T["Haight-Ashbury"]["Fisherman's Wharf"] = 23
T["Haight-Ashbury"]["Financial District"] = 21
T["Haight-Ashbury"]["Russian Hill"] = 17
T["Haight-Ashbury"]["Marina District"] = 17
T["Haight-Ashbury"]["Richmond District"] = 10
T["Haight-Ashbury"]["Pacific Heights"] = 12
T["Haight-Ashbury"]["Presidio"] = 15
T["Haight-Ashbury"]["Nob Hill"] = 15
T["Haight-Ashbury"]["The Castro"] = 6

# Presidio outgoing
T["Presidio"]["Embarcadero"] = 20
T["Presidio"]["Fisherman's Wharf"] = 19
T["Presidio"]["Financial District"] = 23
T["Presidio"]["Russian Hill"] = 14
T["Presidio"]["Marina District"] = 11
T["Presidio"]["Richmond District"] = 7
T["Presidio"]["Pacific Heights"] = 11
T["Presidio"]["Haight-Ashbury"] = 15
T["Presidio"]["Nob Hill"] = 18
T["Presidio"]["The Castro"] = 21

# Nob Hill outgoing
T["Nob Hill"]["Embarcadero"] = 9
T["Nob Hill"]["Fisherman's Wharf"] = 10
T["Nob Hill"]["Financial District"] = 9
T["Nob Hill"]["Russian Hill"] = 5
T["Nob Hill"]["Marina District"] = 11
T["Nob Hill"]["Richmond District"] = 14
T["Nob Hill"]["Pacific Heights"] = 8
T["Nob Hill"]["Haight-Ashbury"] = 13
T["Nob Hill"]["Presidio"] = 17
T["Nob Hill"]["The Castro"] = 17

# The Castro outgoing
T["The Castro"]["Embarcadero"] = 22
T["The Castro"]["Fisherman's Wharf"] = 24
T["The Castro"]["Financial District"] = 21
T["The Castro"]["Russian Hill"] = 18
T["The Castro"]["Marina District"] = 21
T["The Castro"]["Richmond District"] = 16
T["The Castro"]["Pacific Heights"] = 16
T["The Castro"]["Haight-Ashbury"] = 6
T["The Castro"]["Presidio"] = 20
T["The Castro"]["Nob Hill"] = 16

# Friends with locations, availability windows, and minimum durations
friends = [
    # name, location, avail_start, avail_end, min_duration
    ("Stephanie", "Fisherman's Wharf", hm_to_min(15,30), hm_to_min(22,0), 30),
    ("Lisa", "Financial District", hm_to_min(10,45), hm_to_min(17,15), 15),
    ("Melissa", "Russian Hill", hm_to_min(17,0), hm_to_min(21,45), 120),
    ("Betty", "Marina District", hm_to_min(10,45), hm_to_min(14,15), 60),
    ("Sarah", "Richmond District", hm_to_min(16,15), hm_to_min(19,30), 105),
    ("Daniel", "Pacific Heights", hm_to_min(18,30), hm_to_min(21,45), 60),
    ("Joshua", "Haight-Ashbury", hm_to_min(9,0), hm_to_min(15,30), 15),
    ("Joseph", "Presidio", hm_to_min(7,0), hm_to_min(13,0), 45),
    ("Andrew", "Nob Hill", hm_to_min(19,45), hm_to_min(22,0), 105),
    ("John", "The Castro", hm_to_min(13,15), hm_to_min(19,45), 45),
]

start_loc = "Embarcadero"
arrival_time = hm_to_min(9, 0)

# Build Z3 model
opt = Optimize()

n = len(friends)
s_vars = []
d_vars = []
e_vars = []
sel_vars = []

for i, (name, loc, a, b, mindur) in enumerate(friends):
    s = Int(f"s_{i}")   # start time (minutes)
    d = Int(f"d_{i}")   # duration (minutes)
    e = Int(f"e_{i}")   # end time (minutes)
    sel = Bool(f"sel_{i}")

    s_vars.append(s)
    d_vars.append(d)
    e_vars.append(e)
    sel_vars.append(sel)

    # Domains
    opt.add(And(s >= 0, s <= 24*60))
    opt.add(And(d >= 0, d <= 24*60))
    opt.add(And(e >= 0, e <= 24*60))

    # If selected, must satisfy availability and duration
    opt.add(Implies(sel, s >= a))
    opt.add(Implies(sel, e <= b))
    opt.add(Implies(sel, d >= mindur))
    opt.add(Implies(sel, e == s + d))

    # If selected, must be reachable from start at 9:00 from Embarcadero
    t_from_start = T[start_loc][loc]
    opt.add(Implies(sel, s >= arrival_time + t_from_start))

# Pairwise non-overlap with travel times using ordering booleans
order = {}
for i in range(n):
    for j in range(i+1, n):
        order[(i,j)] = Bool(f"order_{i}_{j}")  # True => i before j. False => j before i.

        loc_i = friends[i][1]
        loc_j = friends[j][1]
        tij = T[loc_i][loc_j]
        tji = T[loc_j][loc_i]

        # If both selected and i before j, then s_j >= e_i + travel(i->j)
        opt.add(Implies(And(sel_vars[i], sel_vars[j], order[(i,j)]), s_vars[j] >= e_vars[i] + tij))
        # If both selected and j before i, then s_i >= e_j + travel(j->i)
        opt.add(Implies(And(sel_vars[i], sel_vars[j], Not(order[(i,j)])), s_vars[i] >= e_vars[j] + tji))

# Objective: maximize number of friends met
opt.maximize(Sum([If(sel_vars[i], 1, 0) for i in range(n)]))

# Optionally, break ties by minimizing final end time (makespan)
makespan = Int("makespan")
opt.add(makespan >= 0)
for i in range(n):
    opt.add(Implies(sel_vars[i], makespan >= e_vars[i]))
opt.minimize(makespan)

# Solve
if opt.check() != sat and opt.check() != 1:
    # Fallback: no solution
    print(json.dumps({"itinerary": []}))
else:
    model = opt.model()
    meetings = []
    for i, (name, loc, a, b, mindur) in enumerate(friends):
        if model.evaluate(sel_vars[i], model_completion=True) == BoolVal(True):
            s = model.evaluate(s_vars[i], model_completion=True).as_long()
            e = model.evaluate(e_vars[i], model_completion=True).as_long()
            meetings.append({
                "person": name,
                "start": s,
                "end": e
            })

    # Sort by start time
    meetings.sort(key=lambda x: x["start"])

    # Build required output format
    itinerary = []
    for m in meetings:
        itinerary.append({
            "action": "meet",
            "person": m["person"],
            "start_time": min_to_hhmm(m["start"]),
            "end_time": min_to_hhmm(m["end"])
        })

    print(json.dumps({"itinerary": itinerary}))