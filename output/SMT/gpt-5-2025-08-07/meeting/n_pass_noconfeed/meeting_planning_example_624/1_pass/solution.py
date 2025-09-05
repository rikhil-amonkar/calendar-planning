import json
from z3 import *

def parse_time_ampm(t):
    t = t.strip().upper()
    # Expected like '9:30AM' or '10:30PM'
    if t.endswith("AM") or t.endswith("PM"):
        ampm = t[-2:]
        hhmm = t[:-2]
        h, m = hhmm.split(":")
        h = int(h)
        m = int(m)
        if ampm == "AM":
            if h == 12:
                h = 0
        else:
            if h != 12:
                h += 12
        return h * 60 + m
    else:
        # 24h 'H:MM'
        h, m = t.split(":")
        return int(h) * 60 + int(m)

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Locations
GGP = "Golden Gate Park"
HAI = "Haight-Ashbury"
WHF = "Fisherman's Wharf"
CAS = "The Castro"
CHI = "Chinatown"
ALA = "Alamo Square"
NOB = "North Beach"
RUS = "Russian Hill"

# Directed travel times in minutes (as provided)
dist = {
    GGP: {HAI:7, WHF:24, CAS:13, CHI:23, ALA:10, NOB:24, RUS:19},
    HAI: {GGP:7, WHF:23, CAS:6, CHI:19, ALA:5, NOB:19, RUS:17},
    WHF: {GGP:25, HAI:22, CAS:26, CHI:12, ALA:20, NOB:6, RUS:7},
    CAS: {GGP:11, HAI:6, WHF:24, CHI:20, ALA:8, NOB:20, RUS:18},
    CHI: {GGP:23, HAI:19, WHF:8, CAS:22, ALA:17, NOB:3, RUS:7},
    ALA: {GGP:9, HAI:5, WHF:19, CAS:8, CHI:16, NOB:15, RUS:13},
    NOB: {GGP:22, HAI:18, WHF:5, CAS:22, CHI:6, ALA:16, RUS:4},
    RUS: {GGP:21, HAI:17, WHF:7, CAS:21, CHI:9, ALA:15, NOB:5},
}

# Friends and constraints
friends = [
    {
        "name": "Carol",
        "location": HAI,
        "avail_start": parse_time_ampm("9:30PM"),
        "avail_end": parse_time_ampm("10:30PM"),
        "min_minutes": 60
    },
    {
        "name": "Laura",
        "location": WHF,
        "avail_start": parse_time_ampm("11:45AM"),
        "avail_end": parse_time_ampm("9:30PM"),
        "min_minutes": 60
    },
    {
        "name": "Karen",
        "location": CAS,
        "avail_start": parse_time_ampm("7:15AM"),
        "avail_end": parse_time_ampm("2:00PM"),
        "min_minutes": 75
    },
    {
        "name": "Elizabeth",
        "location": CHI,
        "avail_start": parse_time_ampm("12:15PM"),
        "avail_end": parse_time_ampm("9:30PM"),
        "min_minutes": 75
    },
    {
        "name": "Deborah",
        "location": ALA,
        "avail_start": parse_time_ampm("12:00PM"),
        "avail_end": parse_time_ampm("3:00PM"),
        "min_minutes": 105
    },
    {
        "name": "Jason",
        "location": NOB,
        "avail_start": parse_time_ampm("2:45PM"),
        "avail_end": parse_time_ampm("7:00PM"),
        "min_minutes": 90
    },
    {
        "name": "Steven",
        "location": RUS,
        "avail_start": parse_time_ampm("2:45PM"),
        "avail_end": parse_time_ampm("6:30PM"),
        "min_minutes": 120
    },
]

n = len(friends)

# Arrival time at Golden Gate Park
arrival_time = parse_time_ampm("9:00AM")

opt = Optimize()
opt.set("opt.priority", "lex")

# Variables per friend
starts = [Int(f"start_{i}") for i in range(n)]
ends = [Int(f"end_{i}") for i in range(n)]
selects = [Bool(f"sel_{i}") for i in range(n)]

# Bounds for time variables
for i in range(n):
    opt.add(starts[i] >= 0, starts[i] <= 24*60)
    opt.add(ends[i] >= 0, ends[i] <= 24*60)

# Meeting duration equals minimum required
for i, f in enumerate(friends):
    opt.add(ends[i] == starts[i] + f["min_minutes"])

# Availability and initial travel feasibility
for i, f in enumerate(friends):
    loc = f["location"]
    # If selected, must be within availability window
    opt.add(Implies(selects[i],
                    And(starts[i] >= f["avail_start"],
                        ends[i] <= f["avail_end"])))
    # If selected, can't start earlier than traveling directly from arrival point at 9:00
    init_travel = dist[GGP][loc]
    opt.add(Implies(selects[i], starts[i] >= arrival_time + init_travel))

# Pairwise ordering and travel-time separation
orders = {}
for i in range(n):
    for j in range(i+1, n):
        o = Bool(f"order_{i}_{j}")  # True means i before j, False means j before i
        orders[(i, j)] = o
        li = friends[i]["location"]
        lj = friends[j]["location"]
        # If both selected and i before j
        opt.add(Implies(And(selects[i], selects[j], o),
                        starts[j] >= ends[i] + dist[li][lj]))
        # If both selected and j before i
        opt.add(Implies(And(selects[i], selects[j], Not(o)),
                        starts[i] >= ends[j] + dist[lj][li]))

# Latest end time (makespan) for tie-breaking
latest_end = Int("latest_end")
opt.add(latest_end >= arrival_time, latest_end <= 24*60)
for i in range(n):
    opt.add(Implies(selects[i], latest_end >= ends[i]))

# Objective 1: maximize number of friends met
total_met = Sum([If(selects[i], 1, 0) for i in range(n)])
opt.maximize(total_met)

# Objective 2: minimize latest end time (finish earlier if same count)
opt.minimize(latest_end)

# Solve
if opt.check() != sat:
    result = {"itinerary": []}
    print(json.dumps(result, ensure_ascii=False))
else:
    model = opt.model()
    chosen = []
    for i, f in enumerate(friends):
        if is_true(model.evaluate(selects[i])):
            s = int(model.evaluate(starts[i]).as_long())
            e = int(model.evaluate(ends[i]).as_long())
            chosen.append((s, {
                "action": "meet",
                "location": f["location"],
                "person": f["name"],
                "start_time": minutes_to_str(s),
                "end_time": minutes_to_str(e),
            }))

    # Sort by start time
    chosen.sort(key=lambda x: x[0])

    itinerary = [entry for _, entry in chosen]
    result = {"itinerary": itinerary}
    print(json.dumps(result, ensure_ascii=False, indent=2))