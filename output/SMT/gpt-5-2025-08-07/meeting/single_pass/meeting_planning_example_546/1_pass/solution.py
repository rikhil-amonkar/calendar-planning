# Solve the SF day scheduling problem with Z3 to maximize the number of friends met.

from z3 import *
import json

def to_min(h, m):
    return h * 60 + m

def minutes_to_hhmm(t):
    h = (t // 60) % 24
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Travel times (directed, minutes)
travel = {
    "Embarcadero": {
        "Richmond District": 21,
        "Union Square": 10,
        "Financial District": 5,
        "Pacific Heights": 11,
        "Nob Hill": 10,
        "Bayview": 21,
    },
    "Richmond District": {
        "Embarcadero": 19,
        "Union Square": 21,
        "Financial District": 22,
        "Pacific Heights": 10,
        "Nob Hill": 17,
        "Bayview": 26,
    },
    "Union Square": {
        "Embarcadero": 11,
        "Richmond District": 20,
        "Financial District": 9,
        "Pacific Heights": 15,
        "Nob Hill": 9,
        "Bayview": 15,
    },
    "Financial District": {
        "Embarcadero": 4,
        "Richmond District": 21,
        "Union Square": 9,
        "Pacific Heights": 13,
        "Nob Hill": 8,
        "Bayview": 19,
    },
    "Pacific Heights": {
        "Embarcadero": 10,
        "Richmond District": 12,
        "Union Square": 12,
        "Financial District": 13,
        "Nob Hill": 8,
        "Bayview": 22,
    },
    "Nob Hill": {
        "Embarcadero": 9,
        "Richmond District": 14,
        "Union Square": 7,
        "Financial District": 9,
        "Pacific Heights": 8,
        "Bayview": 19,
    },
    "Bayview": {
        "Embarcadero": 19,
        "Richmond District": 25,
        "Union Square": 17,
        "Financial District": 19,
        "Pacific Heights": 23,
        "Nob Hill": 20,
    },
}

# Friends: name, location, availability window [start, end], and minimum meeting duration
friends = [
    {"name": "Kenneth", "loc": "Richmond District", "start": to_min(21, 15), "end": to_min(22, 0),  "dur": 30},
    {"name": "Lisa",    "loc": "Union Square",      "start": to_min(9, 0),   "end": to_min(16, 30), "dur": 45},
    {"name": "Joshua",  "loc": "Financial District","start": to_min(12, 0),  "end": to_min(15, 15), "dur": 15},
    {"name": "Nancy",   "loc": "Pacific Heights",   "start": to_min(8, 0),   "end": to_min(11, 30), "dur": 90},
    {"name": "Andrew",  "loc": "Nob Hill",          "start": to_min(11, 30), "end": to_min(20, 15), "dur": 60},
    {"name": "John",    "loc": "Bayview",           "start": to_min(16, 45), "end": to_min(21, 30), "dur": 75},
]

start_loc = "Embarcadero"
start_time = to_min(9, 0)

n = len(friends)
s = [Int(f"s_{i}") for i in range(n)]         # start times
v = [Bool(f"v_{i}") for i in range(n)]        # visit decision

opt = Optimize()

# Basic constraints: domains, availability windows, and earliest arrival from Embarcadero
for i, f in enumerate(friends):
    opt.add(s[i] >= 0, s[i] <= 24 * 60)
    # If visited, must be within their window and after travel from start
    opt.add(Implies(v[i], And(
        s[i] >= f["start"],
        s[i] + f["dur"] <= f["end"],
        s[i] >= start_time + travel[start_loc][f["loc"]]
    )))

# Disjunctive sequencing with travel times between any visited pair
for i in range(n):
    for j in range(i + 1, n):
        fi, fj = friends[i], friends[j]
        tij = travel[fi["loc"]][fj["loc"]]
        tji = travel[fj["loc"]][fi["loc"]]
        # If both visited, either i ends + travel_ij before j starts OR j ends + travel_ji before i starts
        opt.add(Implies(And(v[i], v[j]),
                        Or(s[i] + fi["dur"] + tij <= s[j],
                           s[j] + fj["dur"] + tji <= s[i])))

# Objective: maximize number of friends met
count = Sum([If(v[i], 1, 0) for i in range(n)])
opt.maximize(count)

# Secondary objective: minimize latest end time among visited, to keep schedule tight
latest_end = Int("latest_end")
opt.add(latest_end >= start_time)
for i, f in enumerate(friends):
    opt.add(Implies(v[i], latest_end >= s[i] + f["dur"]))
opt.minimize(latest_end)

# Solve
if opt.check() != sat:
    raise RuntimeError("No feasible schedule found.")

m = opt.model()

# Build itinerary
itinerary = []
for i, f in enumerate(friends):
    if is_true(m[v[i]]):
        start = m[s[i]].as_long()
        end = start + f["dur"]
        itinerary.append({
            "action": "meet",
            "person": f["name"],
            "start_time": minutes_to_hhmm(start),
            "end_time": minutes_to_hhmm(end)
        })

# Sort by chronological order
itinerary.sort(key=lambda e: e["start_time"])

print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))