# Requires: z3-solver
# pip install z3-solver

from z3 import Optimize, Int, Bool, If, Or, And, Sum
import json

def time_to_minutes(tstr):
    # tstr like "HH:MM" in 24h or with AM/PM handler isn't needed here
    h, m = map(int, tstr.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

# Locations
RICHMOND = "Richmond District"
MARINA = "Marina District"
CHINATOWN = "Chinatown"
FINANCIAL = "Financial District"
BAYVIEW = "Bayview"
UNION_SQ = "Union Square"

# Directed travel times (minutes)
t = {
    RICHMOND: {MARINA: 9, CHINATOWN: 20, FINANCIAL: 22, BAYVIEW: 26, UNION_SQ: 21},
    MARINA: {RICHMOND: 11, CHINATOWN: 16, FINANCIAL: 17, BAYVIEW: 27, UNION_SQ: 16},
    CHINATOWN: {RICHMOND: 20, MARINA: 12, FINANCIAL: 5, BAYVIEW: 22, UNION_SQ: 7},
    FINANCIAL: {RICHMOND: 21, MARINA: 15, CHINATOWN: 5, BAYVIEW: 19, UNION_SQ: 9},
    BAYVIEW: {RICHMOND: 25, MARINA: 25, CHINATOWN: 18, FINANCIAL: 19, UNION_SQ: 17},
    UNION_SQ: {RICHMOND: 20, MARINA: 18, CHINATOWN: 7, FINANCIAL: 9, BAYVIEW: 15},
}

# People and constraints
people = [
    {
        "name": "Kimberly",
        "loc": MARINA,
        "avail_start": time_to_minutes("13:15"),
        "avail_end": time_to_minutes("16:45"),
        "min_meet": 15,
    },
    {
        "name": "Robert",
        "loc": CHINATOWN,
        "avail_start": time_to_minutes("12:15"),
        "avail_end": time_to_minutes("20:15"),
        "min_meet": 15,
    },
    {
        "name": "Rebecca",
        "loc": FINANCIAL,
        "avail_start": time_to_minutes("13:15"),
        "avail_end": time_to_minutes("16:45"),
        "min_meet": 75,
    },
    {
        "name": "Margaret",
        "loc": BAYVIEW,
        "avail_start": time_to_minutes("09:30"),
        "avail_end": time_to_minutes("13:30"),
        "min_meet": 30,
    },
    {
        "name": "Kenneth",
        "loc": UNION_SQ,
        "avail_start": time_to_minutes("19:30"),
        "avail_end": time_to_minutes("21:15"),
        "min_meet": 75,
    },
]

START_LOC = RICHMOND
START_TIME = time_to_minutes("09:00")

opt = Optimize()

start_vars = {}
end_vars = {}
meet_vars = {}

HORIZON = 24 * 60

for p in people:
    s = Int(f"start_{p['name']}")
    e = Int(f"end_{p['name']}")
    m = Bool(f"meet_{p['name']}")
    start_vars[p['name']] = s
    end_vars[p['name']] = e
    meet_vars[p['name']] = m

    # Bounds
    opt.add(s >= 0, s <= HORIZON, e >= 0, e <= HORIZON)

    # If meeting, respect availability and duration
    opt.add(If(m, And(
        s >= p["avail_start"],
        e <= p["avail_end"],
        e - s >= p["min_meet"],
        s < e
    ), And(e == 0, s == 0)  # if not meeting, set to 0 for clean objective minimization
    ))

    # Feasibility from start location: cannot start before physically reachable from Richmond
    # This is a safe necessary condition even if there are prior meetings.
    opt.add(If(m, s >= START_TIME + t[START_LOC][p["loc"]], True))

# Pairwise disjunctive travel constraints
for i in range(len(people)):
    for j in range(i + 1, len(people)):
        pi = people[i]
        pj = people[j]
        si = start_vars[pi["name"]]
        ei = end_vars[pi["name"]]
        sj = start_vars[pj["name"]]
        ej = end_vars[pj["name"]]
        mi = meet_vars[pi["name"]]
        mj = meet_vars[pj["name"]]

        # If both meetings happen, enforce travel-time-separated ordering
        opt.add(Or(Not(And(mi, mj)),
                   Or(ei + t[pi["loc"]][pj["loc"]] <= sj,
                      ej + t[pj["loc"]][pi["loc"]] <= si)))

# Objective 1: maximize number of people met
total_met = Sum([If(meet_vars[p["name"]], 1, 0) for p in people])
h1 = opt.maximize(total_met)

# Objective 2: among maxima, minimize sum of end times (earlier, tighter schedule)
total_end = Sum([If(meet_vars[p["name"]], end_vars[p["name"]], 0) for p in people])
h2 = opt.minimize(total_end)

# Solve
opt.check()
model = opt.model()

# Extract itinerary
itinerary = []
for p in people:
    if model.evaluate(meet_vars[p["name"]]).is_true():
        s_val = model.evaluate(start_vars[p["name"]]).as_long()
        e_val = model.evaluate(end_vars[p["name"]]).as_long()
        itinerary.append({
            "action": "meet",
            "person": p["name"],
            "start_time": minutes_to_time(s_val),
            "end_time": minutes_to_time(e_val),
        })

# Sort by start time
itinerary.sort(key=lambda x: x["start_time"])

print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))