import json
from z3 import *

def time_to_min(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Data
locations = [
    "Alamo Square", "Russian Hill", "Presidio", "Chinatown",
    "Sunset District", "The Castro", "Embarcadero", "Golden Gate Park"
]

# Travel times in minutes (directed)
travel = {
    "Alamo Square": {
        "Russian Hill": 13, "Presidio": 18, "Chinatown": 16,
        "Sunset District": 16, "The Castro": 8, "Embarcadero": 17,
        "Golden Gate Park": 9
    },
    "Russian Hill": {
        "Alamo Square": 15, "Presidio": 14, "Chinatown": 9,
        "Sunset District": 23, "The Castro": 21, "Embarcadero": 8,
        "Golden Gate Park": 21
    },
    "Presidio": {
        "Alamo Square": 18, "Russian Hill": 14, "Chinatown": 21,
        "Sunset District": 15, "The Castro": 21, "Embarcadero": 20,
        "Golden Gate Park": 12
    },
    "Chinatown": {
        "Alamo Square": 17, "Russian Hill": 7, "Presidio": 19,
        "Sunset District": 29, "The Castro": 22, "Embarcadero": 5,
        "Golden Gate Park": 23
    },
    "Sunset District": {
        "Alamo Square": 17, "Russian Hill": 24, "Presidio": 16,
        "Chinatown": 30, "The Castro": 17, "Embarcadero": 31,
        "Golden Gate Park": 11
    },
    "The Castro": {
        "Alamo Square": 8, "Russian Hill": 18, "Presidio": 20,
        "Chinatown": 20, "Sunset District": 17, "Embarcadero": 22,
        "Golden Gate Park": 11
    },
    "Embarcadero": {
        "Alamo Square": 19, "Russian Hill": 8, "Presidio": 20,
        "Chinatown": 7, "Sunset District": 30, "The Castro": 25,
        "Golden Gate Park": 25
    },
    "Golden Gate Park": {
        "Alamo Square": 10, "Russian Hill": 19, "Presidio": 11,
        "Chinatown": 23, "Sunset District": 10, "The Castro": 13,
        "Embarcadero": 25
    }
}

def get_travel(a, b):
    if a == b:
        return 0
    return travel[a][b]

start_location = "Alamo Square"
start_time = time_to_min("9:00")

people = [
    {
        "name": "Emily",
        "location": "Russian Hill",
        "window_start": time_to_min("12:15"),
        "window_end": time_to_min("14:15"),
        "min_duration": 105
    },
    {
        "name": "Mark",
        "location": "Presidio",
        "window_start": time_to_min("14:45"),
        "window_end": time_to_min("19:30"),
        "min_duration": 60
    },
    {
        "name": "Deborah",
        "location": "Chinatown",
        "window_start": time_to_min("7:30"),
        "window_end": time_to_min("15:30"),
        "min_duration": 45
    },
    {
        "name": "Margaret",
        "location": "Sunset District",
        "window_start": time_to_min("21:30"),
        "window_end": time_to_min("22:30"),
        "min_duration": 60
    },
    {
        "name": "George",
        "location": "The Castro",
        "window_start": time_to_min("7:30"),
        "window_end": time_to_min("14:15"),
        "min_duration": 60
    },
    {
        "name": "Andrew",
        "location": "Embarcadero",
        "window_start": time_to_min("20:15"),
        "window_end": time_to_min("22:00"),
        "min_duration": 75
    },
    {
        "name": "Steven",
        "location": "Golden Gate Park",
        "window_start": time_to_min("11:15"),
        "window_end": time_to_min("21:15"),
        "min_duration": 105
    }
]

names = [p["name"] for p in people]
idx = {p["name"]: i for i, p in enumerate(people)}

opt = Optimize()

# Variables
meet = {p["name"]: Bool(f"meet_{p['name']}") for p in people}
start_vars = {p["name"]: Int(f"start_{p['name']}") for p in people}
end_vars = {p["name"]: Int(f"end_{p['name']}") for p in people}

# Domain constraints
for p in people:
    n = p["name"]
    s = start_vars[n]
    e = end_vars[n]
    opt.add(s >= 0, e >= 0, s <= 24 * 60, e <= 24 * 60, e >= s)
    # If meeting, enforce window and duration
    opt.add(Implies(meet[n], And(
        s >= p["window_start"],
        e <= p["window_end"],
        e - s >= p["min_duration"],
        # Must be reachable from the starting point at 9:00
        s >= start_time + get_travel(start_location, p["location"])
    )))
    # If not meeting, collapse interval
    opt.add(Implies(Not(meet[n]), And(s == 0, e == 0)))

# Pairwise ordering and travel-time separation
order = {}
for i in range(len(people)):
    for j in range(len(people)):
        if i >= j:
            continue
        ni = people[i]["name"]
        nj = people[j]["name"]
        oij = Bool(f"order_{ni}_before_{nj}")
        oji = Bool(f"order_{nj}_before_{ni}")
        order[(ni, nj)] = oij
        order[(nj, ni)] = oji

        # If both meetings occur, exactly one order is true
        both = And(meet[ni], meet[nj])
        opt.add(Implies(both, Xor(oij, oji)))
        # If either is not met, no order is set
        opt.add(Implies(Not(both), And(Not(oij), Not(oji))))

        # Travel-time separation constraints if ordered
        ti_to_j = get_travel(people[i]["location"], people[j]["location"])
        tj_to_i = get_travel(people[j]["location"], people[i]["location"])
        opt.add(Implies(And(both, oij), end_vars[ni] + ti_to_j <= start_vars[nj]))
        opt.add(Implies(And(both, oji), end_vars[nj] + tj_to_i <= start_vars[ni]))

# Objective: maximize number of friends met
meet_count = Sum([If(meet[p["name"]], 1, 0) for p in people])
opt.maximize(meet_count)

# Secondary objective: maximize total meeting time
total_meeting_time = Sum([If(meet[p["name"]], end_vars[p["name"]] - start_vars[p["name"]], 0) for p in people])
opt.maximize(total_meeting_time)

if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
else:
    model = opt.model()
    itinerary = []
    for p in people:
        n = p["name"]
        if is_true(model.eval(meet[n])):
            s_val = model.eval(start_vars[n]).as_long()
            e_val = model.eval(end_vars[n]).as_long()
            itinerary.append({
                "action": "meet",
                "location": p["location"],
                "person": n,
                "start_time": min_to_time(s_val),
                "end_time": min_to_time(e_val)
            })
    # Sort by start_time
    itinerary.sort(key=lambda x: time_to_min(x["start_time"]))

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))