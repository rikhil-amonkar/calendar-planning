# SOLUTION:
from z3 import *
import json

def minutes(h, m):
    return h * 60 + m

def format_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Travel times (directed, in minutes)
travel = {
    "Nob Hill": {
        "Embarcadero": 9,
        "The Castro": 17,
        "Haight-Ashbury": 13,
        "Union Square": 7,
        "North Beach": 8,
        "Pacific Heights": 8,
        "Chinatown": 6,
        "Golden Gate Park": 17,
        "Marina District": 11,
        "Russian Hill": 5,
    },
    "Embarcadero": {
        "Nob Hill": 10,
        "The Castro": 25,
        "Haight-Ashbury": 21,
        "Union Square": 10,
        "North Beach": 5,
        "Pacific Heights": 11,
        "Chinatown": 7,
        "Golden Gate Park": 25,
        "Marina District": 12,
        "Russian Hill": 8,
    },
    "The Castro": {
        "Nob Hill": 16,
        "Embarcadero": 22,
        "Haight-Ashbury": 6,
        "Union Square": 19,
        "North Beach": 20,
        "Pacific Heights": 16,
        "Chinatown": 22,
        "Golden Gate Park": 11,
        "Marina District": 21,
        "Russian Hill": 18,
    },
    "Haight-Ashbury": {
        "Nob Hill": 15,
        "Embarcadero": 20,
        "The Castro": 6,
        "Union Square": 19,
        "North Beach": 19,
        "Pacific Heights": 12,
        "Chinatown": 19,
        "Golden Gate Park": 7,
        "Marina District": 17,
        "Russian Hill": 17,
    },
    "Union Square": {
        "Nob Hill": 9,
        "Embarcadero": 11,
        "The Castro": 17,
        "Haight-Ashbury": 18,
        "North Beach": 10,
        "Pacific Heights": 15,
        "Chinatown": 7,
        "Golden Gate Park": 22,
        "Marina District": 18,
        "Russian Hill": 13,
    },
    "North Beach": {
        "Nob Hill": 7,
        "Embarcadero": 6,
        "The Castro": 23,
        "Haight-Ashbury": 18,
        "Union Square": 7,
        "Pacific Heights": 8,
        "Chinatown": 6,
        "Golden Gate Park": 22,
        "Marina District": 9,
        "Russian Hill": 4,
    },
    "Pacific Heights": {
        "Nob Hill": 8,
        "Embarcadero": 10,
        "The Castro": 16,
        "Haight-Ashbury": 11,
        "Union Square": 12,
        "North Beach": 9,
        "Chinatown": 11,
        "Golden Gate Park": 15,
        "Marina District": 6,
        "Russian Hill": 7,
    },
    "Chinatown": {
        "Nob Hill": 9,
        "Embarcadero": 5,
        "The Castro": 22,
        "Haight-Ashbury": 19,
        "Union Square": 7,
        "North Beach": 3,
        "Pacific Heights": 10,
        "Golden Gate Park": 23,
        "Marina District": 12,
        "Russian Hill": 7,
    },
    "Golden Gate Park": {
        "Nob Hill": 20,
        "Embarcadero": 25,
        "The Castro": 13,
        "Haight-Ashbury": 7,
        "Union Square": 22,
        "North Beach": 23,
        "Pacific Heights": 16,
        "Chinatown": 23,
        "Marina District": 16,
        "Russian Hill": 19,
    },
    "Marina District": {
        "Nob Hill": 12,
        "Embarcadero": 14,
        "The Castro": 22,
        "Haight-Ashbury": 16,
        "Union Square": 16,
        "North Beach": 11,
        "Pacific Heights": 7,
        "Chinatown": 15,
        "Golden Gate Park": 18,
        "Russian Hill": 8,
    },
    "Russian Hill": {
        "Nob Hill": 5,
        "Embarcadero": 8,
        "The Castro": 21,
        "Haight-Ashbury": 17,
        "Union Square": 10,
        "North Beach": 5,
        "Pacific Heights": 7,
        "Chinatown": 9,
        "Golden Gate Park": 21,
        "Marina District": 7,
    },
}

# Participants: name, location, (start, end) in minutes, minimum duration in minutes
participants = {
    "Mary": {
        "location": "Embarcadero",
        "window": (minutes(20, 0), minutes(21, 15)),
        "min_duration": 75,
    },
    "Kenneth": {
        "location": "The Castro",
        "window": (minutes(11, 15), minutes(19, 15)),
        "min_duration": 30,
    },
    "Joseph": {
        "location": "Haight-Ashbury",
        "window": (minutes(20, 0), minutes(22, 0)),
        "min_duration": 120,
    },
    "Sarah": {
        "location": "Union Square",
        "window": (minutes(11, 45), minutes(14, 30)),
        "min_duration": 90,
    },
    "Thomas": {
        "location": "North Beach",
        "window": (minutes(19, 15), minutes(19, 45)),
        "min_duration": 15,
    },
    "Daniel": {
        "location": "Pacific Heights",
        "window": (minutes(13, 45), minutes(20, 30)),
        "min_duration": 15,
    },
    "Richard": {
        "location": "Chinatown",
        "window": (minutes(8, 0), minutes(18, 45)),
        "min_duration": 30,
    },
    "Mark": {
        "location": "Golden Gate Park",
        "window": (minutes(17, 30), minutes(21, 30)),
        "min_duration": 120,
    },
    "David": {
        "location": "Marina District",
        "window": (minutes(20, 0), minutes(21, 0)),
        "min_duration": 60,
    },
    "Karen": {
        "location": "Russian Hill",
        "window": (minutes(13, 15), minutes(18, 30)),
        "min_duration": 120,
    },
}

start_location = "Nob Hill"
start_time = minutes(9, 0)

# Setup Z3 Optimize
opt = Optimize()

# Variables
start_vars = {}  # start time of meeting
dur_vars = {}    # duration of meeting
meet_vars = {}   # whether we meet this person

HORIZON = minutes(23, 59)

for name, info in participants.items():
    s = Int(f"s_{name}")
    d = Int(f"d_{name}")
    m = Bool(f"meet_{name}")
    start_vars[name] = s
    dur_vars[name] = d
    meet_vars[name] = m

    w_start, w_end = info["window"]
    min_d = info["min_duration"]

    # General bounds
    opt.add(And(s >= 0, s <= HORIZON))
    opt.add(And(d >= 0, d <= HORIZON))

    # If meeting, enforce window and minimums
    opt.add(Implies(m, s >= w_start))
    opt.add(Implies(m, s + d <= w_end))
    opt.add(Implies(m, d >= min_d))
    opt.add(Implies(m, d <= (w_end - w_start)))

    # Optional: If not meeting, zero duration
    opt.add(Implies(Not(m), d == 0))

    # Reachability from start location at day start (safe lower bound)
    loc = info["location"]
    # Some locations might not exist in travel dict from start; but we have all
    t_from_start = travel[start_location][loc]
    opt.add(Implies(m, s >= start_time + t_from_start))

# Pairwise non-overlap with travel times
names = list(participants.keys())
for i in range(len(names)):
    for j in range(i + 1, len(names)):
        ni = names[i]
        nj = names[j]
        loc_i = participants[ni]["location"]
        loc_j = participants[nj]["location"]
        travel_ij = travel[loc_i][loc_j]
        travel_ji = travel[loc_j][loc_i]
        si = start_vars[ni]
        sj = start_vars[nj]
        di = dur_vars[ni]
        dj = dur_vars[nj]
        mi = meet_vars[ni]
        mj = meet_vars[nj]
        # If meeting both, they must be sequenced with travel buffer
        opt.add(Implies(And(mi, mj),
                        Or(si + di + travel_ij <= sj,
                           sj + dj + travel_ji <= si)))

# Last end time for secondary objective
last_end = Int("last_end")
opt.add(last_end >= start_time)
for name in names:
    opt.add(Implies(meet_vars[name], last_end >= start_vars[name] + dur_vars[name]))

# Objective: maximize number of meetings, then minimize last end time
total_meetings = Sum([If(meet_vars[name], IntVal(1), IntVal(0)) for name in names])
h1 = opt.maximize(total_meetings)
h2 = opt.minimize(last_end)

# Solve
if opt.check() != sat:
    # Fallback: no feasible schedule
    print(json.dumps({"itinerary": []}))
    exit(0)

model = opt.model()

# Collect chosen meetings
chosen = []
for name in names:
    if is_true(model.evaluate(meet_vars[name])):
        s_val = model.evaluate(start_vars[name]).as_long()
        d_val = model.evaluate(dur_vars[name]).as_long()
        e_val = s_val + d_val
        chosen.append({
            "action": "meet",
            "location": participants[name]["location"],
            "person": name,
            "start_time": format_time(s_val),
            "end_time": format_time(e_val),
            "_start": s_val  # for sorting
        })

# Sort by start time
chosen.sort(key=lambda x: x["_start"])
for item in chosen:
    item.pop("_start", None)

# Output JSON
print(json.dumps({"itinerary": chosen}, ensure_ascii=False))