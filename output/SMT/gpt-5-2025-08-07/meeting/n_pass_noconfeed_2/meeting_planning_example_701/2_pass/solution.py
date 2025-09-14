import json
from z3 import Optimize, Int, Bool, If, And, Or, Implies, Sum, sat, is_true

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Locations
locs = [
    "Mission District",
    "The Castro",
    "Nob Hill",
    "Presidio",
    "Marina District",
    "Pacific Heights",
    "Golden Gate Park",
    "Chinatown",
    "Richmond District",
]

# Directed travel times in minutes
travel = {
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Richmond District"): 20,

    ("The Castro", "Mission District"): 7,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Richmond District"): 16,

    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Richmond District"): 14,

    ("Presidio", "Mission District"): 26,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Richmond District"): 7,

    ("Marina District", "Mission District"): 20,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Richmond District"): 11,

    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Richmond District"): 12,

    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Richmond District"): 7,

    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Richmond District"): 20,

    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Chinatown"): 20,
}

# People, locations, availability, and minimum meeting durations
people = [
    {
        "name": "Lisa",
        "location": "The Castro",
        "avail_start": minutes(19, 15),
        "avail_end": minutes(21, 15),
        "min_meet": 120,
    },
    {
        "name": "Daniel",
        "location": "Nob Hill",
        "avail_start": minutes(8, 15),
        "avail_end": minutes(11, 0),
        "min_meet": 15,
    },
    {
        "name": "Elizabeth",
        "location": "Presidio",
        "avail_start": minutes(21, 15),
        "avail_end": minutes(22, 15),
        "min_meet": 45,
    },
    {
        "name": "Steven",
        "location": "Marina District",
        "avail_start": minutes(16, 30),
        "avail_end": minutes(20, 45),
        "min_meet": 90,
    },
    {
        "name": "Timothy",
        "location": "Pacific Heights",
        "avail_start": minutes(12, 0),
        "avail_end": minutes(18, 0),
        "min_meet": 90,
    },
    {
        "name": "Ashley",
        "location": "Golden Gate Park",
        "avail_start": minutes(20, 45),
        "avail_end": minutes(21, 45),
        "min_meet": 60,
    },
    {
        "name": "Kevin",
        "location": "Chinatown",
        "avail_start": minutes(12, 0),
        "avail_end": minutes(19, 0),
        "min_meet": 30,
    },
    {
        "name": "Betty",
        "location": "Richmond District",
        "avail_start": minutes(13, 15),
        "avail_end": minutes(15, 45),
        "min_meet": 30,
    },
]

start_location = "Mission District"
arrival_time = minutes(9, 0)
DAY_END = minutes(23, 59)

# Z3 model
opt = Optimize()

# Variables per person
vars_map = {}
for p in people:
    s = Int(f"s_{p['name']}")
    e = Int(f"e_{p['name']}")
    meet = Bool(f"meet_{p['name']}")
    vars_map[p['name']] = {"s": s, "e": e, "meet": meet, "loc": p["location"]}
    # Domain bounds
    opt.add(s >= 0, s <= DAY_END, e >= 0, e <= DAY_END)
    # If meeting, obey availability and minimum duration
    opt.add(Implies(meet, And(
        s >= p["avail_start"],
        e <= p["avail_end"],
        e > s,
        e - s >= p["min_meet"],
        # Must be reachable from the starting point at the very least
        s >= arrival_time + travel[(start_location, p["location"])]
    )))
    # If not meeting, set times to 0 (to avoid spurious values)
    opt.add(Implies(~meet, And(s == 0, e == 0)))

# No overlap with travel between any two meetings
for i in range(len(people)):
    for j in range(i + 1, len(people)):
        pi = people[i]
        pj = people[j]
        vi = vars_map[pi["name"]]
        vj = vars_map[pj["name"]]
        ti = travel[(pi["location"], pj["location"])]
        tj = travel[(pj["location"], pi["location"])]
        opt.add(Implies(And(vi["meet"], vj["meet"]),
                        Or(vi["e"] + ti <= vj["s"], vj["e"] + tj <= vi["s"])))


# Objectives:
# 1) Maximize number of friends met
meet_vars = [vars_map[p["name"]]["meet"] for p in people]
total_meet_count = Sum([If(m, 1, 0) for m in meet_vars])
opt.maximize(total_meet_count)

# 2) Maximize total meeting minutes
durations = [If(vars_map[p["name"]]["meet"], vars_map[p["name"]]["e"] - vars_map[p["name"]]["s"], 0) for p in people]
total_minutes = Sum(durations)
opt.maximize(total_minutes)

# Solve
if opt.check() != sat:
    result = {"itinerary": []}
    print(json.dumps(result))
else:
    model = opt.model()
    itinerary = []
    for p in people:
        v = vars_map[p["name"]]
        if is_true(model.evaluate(v["meet"])):
            s_val = model.evaluate(v["s"]).as_long()
            e_val = model.evaluate(v["e"]).as_long()
            itinerary.append({
                "action": "meet",
                "location": p["location"],
                "person": p["name"],
                "start_time": fmt_time(s_val),
                "end_time": fmt_time(e_val)
            })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))