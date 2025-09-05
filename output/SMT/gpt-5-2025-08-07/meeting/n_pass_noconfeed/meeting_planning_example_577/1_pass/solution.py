import json
from z3 import Optimize, Int, Or, And, Implies, Sum

def time_to_min(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Locations
HAIGHT = "Haight-Ashbury"
locations = [
    "Haight-Ashbury",
    "Russian Hill",
    "Fisherman's Wharf",
    "Nob Hill",
    "Golden Gate Park",
    "Alamo Square",
    "Pacific Heights",
]

# Directed travel times in minutes
travel = {
    "Haight-Ashbury": {
        "Russian Hill": 17,
        "Fisherman's Wharf": 23,
        "Nob Hill": 15,
        "Golden Gate Park": 7,
        "Alamo Square": 5,
        "Pacific Heights": 12,
    },
    "Russian Hill": {
        "Haight-Ashbury": 17,
        "Fisherman's Wharf": 7,
        "Nob Hill": 5,
        "Golden Gate Park": 21,
        "Alamo Square": 15,
        "Pacific Heights": 7,
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22,
        "Russian Hill": 7,
        "Nob Hill": 11,
        "Golden Gate Park": 25,
        "Alamo Square": 20,
        "Pacific Heights": 12,
    },
    "Nob Hill": {
        "Haight-Ashbury": 13,
        "Russian Hill": 5,
        "Fisherman's Wharf": 11,
        "Golden Gate Park": 17,
        "Alamo Square": 11,
        "Pacific Heights": 8,
    },
    "Golden Gate Park": {
        "Haight-Ashbury": 7,
        "Russian Hill": 19,
        "Fisherman's Wharf": 24,
        "Nob Hill": 20,
        "Alamo Square": 10,
        "Pacific Heights": 16,
    },
    "Alamo Square": {
        "Haight-Ashbury": 5,
        "Russian Hill": 13,
        "Fisherman's Wharf": 19,
        "Nob Hill": 11,
        "Golden Gate Park": 9,
        "Pacific Heights": 10,
    },
    "Pacific Heights": {
        "Haight-Ashbury": 11,
        "Russian Hill": 7,
        "Fisherman's Wharf": 13,
        "Nob Hill": 8,
        "Golden Gate Park": 15,
        "Alamo Square": 10,
    }
}

def get_travel(a, b):
    if a == b:
        return 0
    return travel[a][b]

# Friends data: name, location, availability window, minimum meeting duration
friends = [
    {
        "name": "Stephanie",
        "location": "Russian Hill",
        "avail_start": time_to_min("20:00"),
        "avail_end": time_to_min("20:45"),
        "min_dur": 15
    },
    {
        "name": "Kevin",
        "location": "Fisherman's Wharf",
        "avail_start": time_to_min("19:15"),
        "avail_end": time_to_min("21:45"),
        "min_dur": 75
    },
    {
        "name": "Robert",
        "location": "Nob Hill",
        "avail_start": time_to_min("7:45"),
        "avail_end": time_to_min("10:30"),
        "min_dur": 90
    },
    {
        "name": "Steven",
        "location": "Golden Gate Park",
        "avail_start": time_to_min("8:30"),
        "avail_end": time_to_min("17:00"),
        "min_dur": 75
    },
    {
        "name": "Anthony",
        "location": "Alamo Square",
        "avail_start": time_to_min("7:45"),
        "avail_end": time_to_min("19:45"),
        "min_dur": 15
    },
    {
        "name": "Sandra",
        "location": "Pacific Heights",
        "avail_start": time_to_min("14:45"),
        "avail_end": time_to_min("21:45"),
        "min_dur": 45
    },
]

start_day_time = time_to_min("9:00")  # arrival at Haight-Ashbury
day_end = time_to_min("23:59")

n = len(friends)

opt = Optimize()

# Variables
meet = [Int(f"meet_{i}") for i in range(n)]            # 0/1
s = [Int(f"start_{i}") for i in range(n)]              # start time in minutes
e = [Int(f"end_{i}") for i in range(n)]                # end time in minutes
y0 = [Int(f"y0_{i}") for i in range(n)]                # 0/1: origin -> i
y = [[Int(f"y_{i}_{j}") if i != j else Int(f"y_{i}_{j}_diag") for j in range(n)] for i in range(n)]  # 0/1: i -> j

# Domains and basic constraints
for i in range(n):
    # Binary domains
    opt.add(Or(meet[i] == 0, meet[i] == 1))
    opt.add(Or(y0[i] == 0, y0[i] == 1))
    opt.add(y0[i] <= meet[i])
    # Time domains
    opt.add(s[i] >= 0, s[i] <= day_end)
    opt.add(e[i] >= 0, e[i] <= day_end)
    # If meeting happens, times within availability and duration
    ai = friends[i]["avail_start"]
    bi = friends[i]["avail_end"]
    mind = friends[i]["min_dur"]
    opt.add(Implies(meet[i] == 1, And(s[i] >= ai, e[i] <= bi, e[i] - s[i] >= mind)))
    # If not meeting, times collapsed to 0
    opt.add(Implies(meet[i] == 0, And(s[i] == 0, e[i] == 0)))
    # No self arcs
    for j in range(n):
        if i == j:
            opt.add(y[i][j] == 0)
        else:
            opt.add(Or(y[i][j] == 0, y[i][j] == 1))
            opt.add(y[i][j] <= meet[i])
            opt.add(y[i][j] <= meet[j])

# Predecessor constraints: exactly one predecessor (origin or another) if met
for i in range(n):
    preds_from_others = Sum([y[j][i] for j in range(n) if j != i])
    opt.add(y0[i] + preds_from_others == meet[i])

# Successor constraints: at most one successor if met (forms a single chain)
for i in range(n):
    succs_to_others = Sum([y[i][j] for j in range(n) if j != i])
    opt.add(succs_to_others <= meet[i])

# Only one first meeting after origin
opt.add(Sum(y0) <= 1)

# Temporal implications
for i in range(n):
    loc_i = friends[i]["location"]
    # From origin to i
    t0_i = get_travel(HAIGHT, loc_i)
    opt.add(Implies(y0[i] == 1, s[i] >= start_day_time + t0_i))
    for j in range(n):
        if i == j:
            continue
        loc_j = friends[j]["location"]
        tij = get_travel(loc_i, loc_j)
        # If i precedes j, account for travel and meeting ordering
        opt.add(Implies(y[i][j] == 1, s[j] >= e[i] + tij))

# Objective: maximize number of friends met
opt.maximize(Sum(meet))
# Tie-breaker: maximize total meeting time
opt.maximize(Sum([e[i] - s[i] for i in range(n)]))

if opt.check() != None:
    model = opt.model()
    itinerary = []
    for i in range(n):
        if model.evaluate(meet[i]).as_long() == 1:
            start_min = model.evaluate(s[i]).as_long()
            end_min = model.evaluate(e[i]).as_long()
            itinerary.append({
                "action": "meet",
                "location": friends[i]["location"],
                "person": friends[i]["name"],
                "start_time": min_to_time(start_min),
                "end_time": min_to_time(end_min),
                "start_min": start_min  # temp for sorting
            })
    itinerary.sort(key=lambda x: x["start_min"])
    for it in itinerary:
        del it["start_min"]
    output = {
        "itinerary": itinerary
    }
    print(json.dumps(output, ensure_ascii=False, indent=2))
else:
    print(json.dumps({"itinerary": []}, indent=2))