# pip install z3-solver
from z3 import Optimize, Int, Bool, If, And, Or, Implies, Not, Xor, Sum, is_true
import json

# Travel times (minutes) between neighborhoods (directed)
dist = {
    "Marina District": {
        "Mission District": 20, "Fisherman's Wharf": 10, "Presidio": 10,
        "Union Square": 16, "Sunset District": 19, "Financial District": 17,
        "Haight-Ashbury": 16, "Russian Hill": 8
    },
    "Mission District": {
        "Marina District": 19, "Fisherman's Wharf": 22, "Presidio": 25,
        "Union Square": 15, "Sunset District": 24, "Financial District": 15,
        "Haight-Ashbury": 12, "Russian Hill": 15
    },
    "Fisherman's Wharf": {
        "Marina District": 9, "Mission District": 22, "Presidio": 17,
        "Union Square": 13, "Sunset District": 27, "Financial District": 11,
        "Haight-Ashbury": 22, "Russian Hill": 7
    },
    "Presidio": {
        "Marina District": 11, "Mission District": 26, "Fisherman's Wharf": 19,
        "Union Square": 22, "Sunset District": 15, "Financial District": 23,
        "Haight-Ashbury": 15, "Russian Hill": 14
    },
    "Union Square": {
        "Marina District": 18, "Mission District": 14, "Fisherman's Wharf": 15,
        "Presidio": 24, "Sunset District": 27, "Financial District": 9,
        "Haight-Ashbury": 18, "Russian Hill": 13
    },
    "Sunset District": {
        "Marina District": 21, "Mission District": 25, "Fisherman's Wharf": 29,
        "Presidio": 16, "Union Square": 30, "Financial District": 30,
        "Haight-Ashbury": 15, "Russian Hill": 24
    },
    "Financial District": {
        "Marina District": 15, "Mission District": 17, "Fisherman's Wharf": 10,
        "Presidio": 22, "Union Square": 9, "Sunset District": 30,
        "Haight-Ashbury": 19, "Russian Hill": 11
    },
    "Haight-Ashbury": {
        "Marina District": 17, "Mission District": 11, "Fisherman's Wharf": 23,
        "Presidio": 15, "Union Square": 19, "Sunset District": 15,
        "Financial District": 21, "Russian Hill": 17
    },
    "Russian Hill": {
        "Marina District": 7, "Mission District": 16, "Fisherman's Wharf": 7,
        "Presidio": 14, "Union Square": 10, "Sunset District": 23,
        "Financial District": 11, "Haight-Ashbury": 17
    }
}

# Friend availability, locations, and minimum meeting durations
friends = [
    {"name": "Karen", "loc": "Mission District", "start": "14:15", "end": "22:00", "min_dur": 30},
    {"name": "Richard", "loc": "Fisherman's Wharf", "start": "14:30", "end": "17:30", "min_dur": 30},
    {"name": "Robert", "loc": "Presidio", "start": "21:45", "end": "22:45", "min_dur": 60},
    {"name": "Joseph", "loc": "Union Square", "start": "11:45", "end": "14:45", "min_dur": 120},
    {"name": "Helen", "loc": "Sunset District", "start": "14:45", "end": "20:45", "min_dur": 105},
    {"name": "Elizabeth", "loc": "Financial District", "start": "10:00", "end": "12:45", "min_dur": 75},
    {"name": "Kimberly", "loc": "Haight-Ashbury", "start": "14:15", "end": "17:30", "min_dur": 105},
    {"name": "Ashley", "loc": "Russian Hill", "start": "11:30", "end": "21:30", "min_dur": 45},
]

start_location = "Marina District"
arrive_time_str = "09:00"  # arrival at Marina

def to_minutes_from_9(hhmm: str) -> int:
    hh, mm = map(int, hhmm.split(":"))
    return (hh - 9) * 60 + mm

def to_time_str_from_9(m: int) -> str:
    total = m + 9 * 60
    hh = total // 60
    mm = total % 60
    return f"{hh:02d}:{mm:02d}"

# Preprocess friend windows in minutes from 09:00
for f in friends:
    f["wstart"] = to_minutes_from_9(f["start"])
    f["wend"] = to_minutes_from_9(f["end"])

names = [f["name"] for f in friends]
name_to_idx = {f["name"]: i for i, f in enumerate(friends)}

opt = Optimize()
opt.set(priority='lex')

# Variables
s_vars = {f["name"]: Int(f"s_{f['name']}") for f in friends}   # start times (minutes from 09:00)
meet_vars = {f["name"]: Bool(f"meet_{f['name']}") for f in friends}  # whether to meet

# Basic domain + window + depart-from-start constraints
for f in friends:
    s = s_vars[f["name"]]
    meet = meet_vars[f["name"]]
    dur = f["min_dur"]
    # Start time lower bound (non-negative)
    opt.add(s >= 0)
    # If meeting, must be within window
    opt.add(Implies(meet, And(s >= f["wstart"], s + dur <= f["wend"])))
    # If meeting, must allow travel from start location at 09:00
    opt.add(Implies(meet, s >= dist[start_location][f["loc"]]))

# Pairwise sequencing constraints with travel times
before = {}  # (i,j) -> Bool meaning i before j
for i in range(len(friends)):
    for j in range(i + 1, len(friends)):
        fi = friends[i]
        fj = friends[j]
        ni, nj = fi["name"], fj["name"]
        bi_j = Bool(f"before_{ni}_then_{nj}")
        bj_i = Bool(f"before_{nj}_then_{ni}")
        before[(ni, nj)] = bi_j
        before[(nj, ni)] = bj_i

        meet_i = meet_vars[ni]
        meet_j = meet_vars[nj]
        si = s_vars[ni]
        sj = s_vars[nj]
        di = fi["min_dur"]
        dj = fj["min_dur"]
        tij = dist[fi["loc"]][fj["loc"]]
        tji = dist[fj["loc"]][fi["loc"]]

        # If both met, exactly one of the orders must hold
        opt.add(Implies(And(meet_i, meet_j), Xor(bi_j, bj_i)))
        # If not both met, neither order holds (to avoid unintended constraints)
        opt.add(Implies(Not(And(meet_i, meet_j)), And(Not(bi_j), Not(bj_i))))
        # Timing implications with travel times
        opt.add(Implies(bi_j, sj >= si + di + tij))
        opt.add(Implies(bj_i, si >= sj + dj + tji))

# Objective 1: maximize number of friends met
meet_count = Sum([If(meet_vars[nm], 1, 0) for nm in names])
opt.maximize(meet_count)

# Objective 2: minimize total start times of attended meetings (bias to earlier schedule)
opt.minimize(Sum([If(meet_vars[nm], s_vars[nm], 0) for nm in names]))

# Objectives 3+: tie-breakers to steer to a specific consistent earliest path
tie_order = ["Elizabeth", "Joseph", "Kimberly", "Richard", "Ashley", "Karen", "Helen", "Robert"]
for nm in tie_order:
    opt.minimize(s_vars[nm])

# Solve
assert opt.check() == 1  # sat

model = opt.model()

# Build itinerary
itinerary = []
for f in friends:
    name = f["name"]
    if is_true(model[meet_vars[name]]):
        s = model[s_vars[name]].as_long()
        e = s + f["min_dur"]
        itinerary.append({
            "name": name,
            "start": s,
            "end": e
        })

# Sort by start time
itinerary.sort(key=lambda x: x["start"])

# Format as required JSON
output = {"itinerary": []}
for item in itinerary:
    output["itinerary"].append({
        "action": "meet",
        "person": item["name"],
        "start_time": to_time_str_from_9(item["start"]),
        "end_time": to_time_str_from_9(item["end"])
    })

print(json.dumps(output))