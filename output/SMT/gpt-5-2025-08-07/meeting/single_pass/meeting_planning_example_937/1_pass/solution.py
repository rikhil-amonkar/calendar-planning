# Solve the scheduling problem with Z3 to maximize the number of friends met
# Subject to travel times and availability windows.

from z3 import *
import json

# Time helper
def to_minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Travel times (minutes), directed
T = {
    "Russian Hill": {
        "Sunset District": 23, "Union Square": 10, "Nob Hill": 5, "Marina District": 7,
        "Richmond District": 14, "Financial District": 11, "Embarcadero": 8, "The Castro": 21,
        "Alamo Square": 15, "Presidio": 14
    },
    "Sunset District": {
        "Russian Hill": 24, "Union Square": 30, "Nob Hill": 27, "Marina District": 21,
        "Richmond District": 12, "Financial District": 30, "Embarcadero": 30, "The Castro": 17,
        "Alamo Square": 17, "Presidio": 16
    },
    "Union Square": {
        "Russian Hill": 13, "Sunset District": 27, "Nob Hill": 9, "Marina District": 18,
        "Richmond District": 20, "Financial District": 9, "Embarcadero": 11, "The Castro": 17,
        "Alamo Square": 15, "Presidio": 24
    },
    "Nob Hill": {
        "Russian Hill": 5, "Sunset District": 24, "Union Square": 7, "Marina District": 11,
        "Richmond District": 14, "Financial District": 9, "Embarcadero": 9, "The Castro": 17,
        "Alamo Square": 11, "Presidio": 17
    },
    "Marina District": {
        "Russian Hill": 8, "Sunset District": 19, "Union Square": 16, "Nob Hill": 12,
        "Richmond District": 11, "Financial District": 17, "Embarcadero": 14, "The Castro": 22,
        "Alamo Square": 15, "Presidio": 10
    },
    "Richmond District": {
        "Russian Hill": 13, "Sunset District": 11, "Union Square": 21, "Nob Hill": 17,
        "Marina District": 9, "Financial District": 22, "Embarcadero": 19, "The Castro": 16,
        "Alamo Square": 13, "Presidio": 7
    },
    "Financial District": {
        "Russian Hill": 11, "Sunset District": 30, "Union Square": 9, "Nob Hill": 8,
        "Marina District": 15, "Richmond District": 21, "Embarcadero": 4, "The Castro": 20,
        "Alamo Square": 17, "Presidio": 22
    },
    "Embarcadero": {
        "Russian Hill": 8, "Sunset District": 30, "Union Square": 10, "Nob Hill": 10,
        "Marina District": 12, "Richmond District": 21, "Financial District": 5, "The Castro": 22,
        "Alamo Square": 16, "Presidio": 20
    },
    "The Castro": {
        "Russian Hill": 18, "Sunset District": 17, "Union Square": 19, "Nob Hill": 16,
        "Marina District": 21, "Richmond District": 16, "Financial District": 21, "Embarcadero": 22,
        "Alamo Square": 8, "Presidio": 20
    },
    "Alamo Square": {
        "Russian Hill": 13, "Sunset District": 16, "Union Square": 14, "Nob Hill": 11,
        "Marina District": 15, "Richmond District": 11, "Financial District": 17, "Embarcadero": 16,
        "The Castro": 8, "Presidio": 17
    },
    "Presidio": {
        "Russian Hill": 14, "Sunset District": 15, "Union Square": 22, "Nob Hill": 18,
        "Marina District": 11, "Richmond District": 7, "Financial District": 23, "Embarcadero": 20,
        "The Castro": 21, "Alamo Square": 19
    }
}

# People data
people = [
    # name, location, window start, window end, min duration
    ("David", "Sunset District", to_minutes(9, 15), to_minutes(22, 0), 15),
    ("Kenneth", "Union Square", to_minutes(21, 15), to_minutes(21, 45), 15),
    ("Patricia", "Nob Hill", to_minutes(15, 0), to_minutes(19, 15), 120),
    ("Mary", "Marina District", to_minutes(14, 45), to_minutes(16, 45), 45),
    ("Charles", "Richmond District", to_minutes(17, 15), to_minutes(21, 0), 15),
    ("Joshua", "Financial District", to_minutes(14, 30), to_minutes(17, 15), 90),
    ("Ronald", "Embarcadero", to_minutes(18, 15), to_minutes(20, 45), 30),
    ("George", "The Castro", to_minutes(14, 15), to_minutes(19, 0), 105),
    ("Kimberly", "Alamo Square", to_minutes(9, 0), to_minutes(14, 30), 105),
    ("William", "Presidio", to_minutes(7, 0), to_minutes(12, 45), 60),
]

start_loc = "Russian Hill"
start_time = to_minutes(9, 0)

# Z3 variables
s = {}   # start time (minutes)
x = {}   # meet this person (0/1)
for name, loc, ws, we, dur in people:
    s[name] = Int(f"s_{name}")
    x[name] = Int(f"x_{name}")

# Pairwise ordering variables
y = {}   # y[i,j] = 1 means i before j, else j before i
for i in range(len(people)):
    for j in range(i+1, len(people)):
        ni = people[i][0]
        nj = people[j][0]
        y[(ni, nj)] = Int(f"y_{ni}_{nj}")

M = 10000

opt = Optimize()

# Domain constraints
for name, loc, ws, we, dur in people:
    opt.add(And(x[name] >= 0, x[name] <= 1))
    opt.add(And(s[name] >= 0, s[name] <= to_minutes(23, 59)))
    # Window constraints active only if we meet them
    opt.add(s[name] >= ws - M * (1 - x[name]))
    opt.add(s[name] + dur <= we + M * (1 - x[name]))
    # Reachability from the starting location
    opt.add(s[name] >= start_time + T[start_loc][loc] - M * (1 - x[name]))

# Pairwise non-overlap with travel
for i in range(len(people)):
    for j in range(i+1, len(people)):
        ni, li, wsi, wei, di = people[i]
        nj, lj, wsj, wej, dj = people[j]
        t_ij = T[li][lj]
        t_ji = T[lj][li]
        # y binary
        opt.add(And(y[(ni, nj)] >= 0, y[(ni, nj)] <= 1))
        # If both meetings selected and i before j
        opt.add(s[nj] >= s[ni] + di + t_ij - M * (1 - y[(ni, nj)]) - M * (1 - x[ni]) - M * (1 - x[nj]))
        # If both meetings selected and j before i
        opt.add(s[ni] >= s[nj] + dj + t_ji - M * y[(ni, nj)] - M * (1 - x[ni]) - M * (1 - x[nj]))

# Objective: maximize number of meetings
opt.maximize(Sum([x[name] for name, *_ in people]))

# Optionally minimize total idle time or end time as tie-breakers (not required)
# opt.minimize(Sum([s[name] for name, *_ in people]))  # weak tie-breaker

res = opt.check()
if res != sat and res != unknown:
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()
    chosen = []
    for name, loc, ws, we, dur in people:
        if m.evaluate(x[name]).as_long() == 1:
            start = m.evaluate(s[name]).as_long()
            end = start + dur
            chosen.append((start, {
                "action": "meet",
                "person": name,
                "start_time": fmt_time(start),
                "end_time": fmt_time(end)
            }))
    chosen.sort(key=lambda t: t[0])
    itinerary = [entry for _, entry in chosen]
    print(json.dumps({"itinerary": itinerary}))