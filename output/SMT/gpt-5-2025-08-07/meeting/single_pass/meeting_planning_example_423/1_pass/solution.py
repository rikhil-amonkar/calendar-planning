# Requires: z3-solver (pip install z3-solver)
from z3 import *
import json

# Time helpers
def to_min(h, m):
    return h*60 + m

def minutes_to_time_str(minutes_from_start):
    # Start is 09:00
    absolute = to_min(9, 0) + minutes_from_start
    hh = absolute // 60
    mm = absolute % 60
    return f"{hh:02d}:{mm:02d}"

# Locations
locations = [
    "Presidio",
    "Richmond District",
    "North Beach",
    "Financial District",
    "Golden Gate Park",
    "Union Square"
]

# Directed travel times in minutes (as provided)
T = {
    "Presidio": {
        "Richmond District": 7,
        "North Beach": 18,
        "Financial District": 23,
        "Golden Gate Park": 12,
        "Union Square": 22
    },
    "Richmond District": {
        "Presidio": 7,
        "North Beach": 17,
        "Financial District": 22,
        "Golden Gate Park": 9,
        "Union Square": 21
    },
    "North Beach": {
        "Presidio": 17,
        "Richmond District": 18,
        "Financial District": 8,
        "Golden Gate Park": 22,
        "Union Square": 7
    },
    "Financial District": {
        "Presidio": 22,
        "Richmond District": 21,
        "North Beach": 7,
        "Golden Gate Park": 23,
        "Union Square": 9
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Richmond District": 7,
        "North Beach": 24,
        "Financial District": 26,
        "Union Square": 22
    },
    "Union Square": {
        "Presidio": 24,
        "Richmond District": 20,
        "North Beach": 10,
        "Financial District": 9,
        "Golden Gate Park": 22
    }
}

# People and constraints
people = [
    {
        "name": "Jason",
        "location": "Richmond District",
        "window_start": to_min(13, 0),   # 13:00
        "window_end": to_min(20, 45),    # 20:45
        "min_duration": 90
    },
    {
        "name": "Melissa",
        "location": "North Beach",
        "window_start": to_min(18, 45),  # 18:45
        "window_end": to_min(20, 15),    # 20:15
        "min_duration": 45
    },
    {
        "name": "Brian",
        "location": "Financial District",
        "window_start": to_min(9, 45),   # 09:45
        "window_end": to_min(21, 45),    # 21:45
        "min_duration": 15
    },
    {
        "name": "Elizabeth",
        "location": "Golden Gate Park",
        # Available from 08:45, but we only start the day at 09:00; we allow 0 as earliest time index.
        "window_start": to_min(8, 45),   # 08:45
        "window_end": to_min(21, 30),    # 21:30
        "min_duration": 105
    },
    {
        "name": "Laura",
        "location": "Union Square",
        "window_start": to_min(14, 15),  # 14:15
        "window_end": to_min(19, 30),    # 19:30
        "min_duration": 75
    }
]

# Convert absolute times (since midnight) into minutes from 09:00 start
day_start_abs = to_min(9, 0)
for p in people:
    p["rel_window_start"] = max(0, p["window_start"] - day_start_abs)  # cannot start before 09:00 arrival
    p["rel_window_end"] = p["window_end"] - day_start_abs

# Horizon up to the latest availability end (relative to 09:00)
horizon = max(p["rel_window_end"] for p in people)
# A safety cushion
horizon = max(horizon, 13*60)  # not strictly needed, but harmless

# Z3 model
opt = Optimize()
opt.set("priority", "lex")  # first maximize count, then minimize makespan

M = 10000  # Big-M

names = [p["name"] for p in people]
name_to_idx = {p["name"]: i for i, p in enumerate(people)}

# Variables per person
s = {}       # start time (relative minutes from 09:00)
e = {}       # end time
meet = {}    # 0/1 whether we meet
for p in people:
    n = p["name"]
    s[n] = Int(f"s_{n}")
    e[n] = Int(f"e_{n}")
    meet[n] = Int(f"meet_{n}")
    # Bounds
    opt.add(s[n] >= 0, s[n] <= horizon)
    opt.add(e[n] >= 0, e[n] <= horizon)
    opt.add(Or(meet[n] == 0, meet[n] == 1))
    # Duration (exact minimum when meeting, zero otherwise)
    opt.add(e[n] - s[n] == p["min_duration"] * meet[n])
    # Availability windows (activated if we meet)
    opt.add(s[n] >= p["rel_window_start"] - M * (1 - meet[n]))
    opt.add(e[n] <= p["rel_window_end"] + M * (1 - meet[n]))
    # Must be able to get there from Presidio at start
    opt.add(s[n] >= T["Presidio"][p["location"]] - M * (1 - meet[n]))

# Pairwise ordering with travel times
x = {}  # x[i,j] = 1 means i before j
for i in range(len(people)):
    for j in range(i+1, len(people)):
        pi = people[i]
        pj = people[j]
        ni = pi["name"]
        nj = pj["name"]
        x[(ni, nj)] = Int(f"x_{ni}_before_{nj}")
        opt.add(Or(x[(ni, nj)] == 0, x[(ni, nj)] == 1))
        # If both are met, enforce either i before j or j before i with travel time
        # s_j >= e_i + travel(i,j) - M*(1 - x_ij) - M*(2 - meet_i - meet_j)
        opt.add(
            s[nj] >= e[ni] + T[pi["location"]][pj["location"]] 
            - M * (1 - x[(ni, nj)]) - M * (2 - meet[ni] - meet[nj])
        )
        # s_i >= e_j + travel(j,i) - M*(x_ij) - M*(2 - meet_i - meet_j)
        opt.add(
            s[ni] >= e[nj] + T[pj["location"]][pi["location"]] 
            - M * (x[(ni, nj)]) - M * (2 - meet[ni] - meet[nj])
        )

# Objectives
total_meet = Sum([meet[p["name"]] for p in people])
opt.maximize(total_meet)

# Secondary: minimize latest end time (makespan) to encourage earlier finish
last_end = Int("last_end")
opt.add(last_end >= 0)
for p in people:
    opt.add(last_end >= e[p["name"]])
opt.minimize(last_end)

# Solve
res = opt.check()
if res != sat:
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()
    # Collect chosen meetings
    chosen = []
    for p in people:
        n = p["name"]
        if m.evaluate(meet[n]).as_long() == 1:
            start_rel = m.evaluate(s[n]).as_long()
            end_rel = m.evaluate(e[n]).as_long()
            chosen.append((start_rel, end_rel, n))
    # Sort by start time
    chosen.sort(key=lambda t: t[0])

    itinerary = []
    for start_rel, end_rel, n in chosen:
        itinerary.append({
            "action": "meet",
            "person": n,
            "start_time": minutes_to_time_str(start_rel),
            "end_time": minutes_to_time_str(end_rel)
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))