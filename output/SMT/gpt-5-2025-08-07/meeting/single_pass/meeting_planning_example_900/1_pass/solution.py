# Requires: z3-solver
# This program finds an itinerary that maximizes the number of friends you can meet,
# respecting travel times, availability windows, and minimum meeting durations.
from z3 import *
import json

def t(h, m):
    return h * 60 + m

def minutes_to_hhmm(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

# Start location/time
START_LOC = "Richmond District"
START_TIME = t(9, 0)  # 09:00

# Directed travel times in minutes between neighborhoods
# Transcribed exactly from the prompt.
T = {}

def add_row(frm, d):
    T[frm] = d

add_row("Richmond District", {
    "The Castro": 16,
    "Nob Hill": 17,
    "Marina District": 9,
    "Pacific Heights": 10,
    "Haight-Ashbury": 10,
    "Mission District": 20,
    "Chinatown": 20,
    "Russian Hill": 13,
    "Alamo Square": 13,
    "Bayview": 27
})
add_row("The Castro", {
    "Richmond District": 16,
    "Nob Hill": 16,
    "Marina District": 21,
    "Pacific Heights": 16,
    "Haight-Ashbury": 6,
    "Mission District": 7,
    "Chinatown": 22,
    "Russian Hill": 18,
    "Alamo Square": 8,
    "Bayview": 19
})
add_row("Nob Hill", {
    "Richmond District": 14,
    "The Castro": 17,
    "Marina District": 11,
    "Pacific Heights": 8,
    "Haight-Ashbury": 13,
    "Mission District": 13,
    "Chinatown": 6,
    "Russian Hill": 5,
    "Alamo Square": 11,
    "Bayview": 19
})
add_row("Marina District", {
    "Richmond District": 11,
    "The Castro": 22,
    "Nob Hill": 12,
    "Pacific Heights": 7,
    "Haight-Ashbury": 16,
    "Mission District": 20,
    "Chinatown": 15,
    "Russian Hill": 8,
    "Alamo Square": 15,
    "Bayview": 27
})
add_row("Pacific Heights", {
    "Richmond District": 12,
    "The Castro": 16,
    "Nob Hill": 8,
    "Marina District": 6,
    "Haight-Ashbury": 11,
    "Mission District": 15,
    "Chinatown": 11,
    "Russian Hill": 7,
    "Alamo Square": 10,
    "Bayview": 22
})
add_row("Haight-Ashbury", {
    "Richmond District": 10,
    "The Castro": 6,
    "Nob Hill": 15,
    "Marina District": 17,
    "Pacific Heights": 12,
    "Mission District": 11,
    "Chinatown": 19,
    "Russian Hill": 17,
    "Alamo Square": 5,
    "Bayview": 18
})
add_row("Mission District", {
    "Richmond District": 20,
    "The Castro": 7,
    "Nob Hill": 12,
    "Marina District": 19,
    "Pacific Heights": 16,
    "Haight-Ashbury": 12,
    "Chinatown": 16,
    "Russian Hill": 15,
    "Alamo Square": 11,
    "Bayview": 14
})
add_row("Chinatown", {
    "Richmond District": 20,
    "The Castro": 22,
    "Nob Hill": 9,
    "Marina District": 12,
    "Pacific Heights": 10,
    "Haight-Ashbury": 19,
    "Mission District": 17,
    "Russian Hill": 7,
    "Alamo Square": 17,
    "Bayview": 20
})
add_row("Russian Hill", {
    "Richmond District": 14,
    "The Castro": 21,
    "Nob Hill": 5,
    "Marina District": 7,
    "Pacific Heights": 7,
    "Haight-Ashbury": 17,
    "Mission District": 16,
    "Chinatown": 9,
    "Alamo Square": 15,
    "Bayview": 23
})
add_row("Alamo Square", {
    "Richmond District": 11,
    "The Castro": 8,
    "Nob Hill": 11,
    "Marina District": 15,
    "Pacific Heights": 10,
    "Haight-Ashbury": 5,
    "Mission District": 10,
    "Chinatown": 15,
    "Russian Hill": 13,
    "Bayview": 16
})
add_row("Bayview", {
    "Richmond District": 25,
    "The Castro": 19,
    "Nob Hill": 20,
    "Marina District": 27,
    "Pacific Heights": 23,
    "Haight-Ashbury": 19,
    "Mission District": 13,
    "Chinatown": 19,
    "Russian Hill": 23,
    "Alamo Square": 16
})

# Friends: name, location, window [start, end], minimum duration
friends = [
    {"name": "Matthew",   "loc": "The Castro",       "win": (t(16,30), t(20,0)),  "min_dur": 45},
    {"name": "Rebecca",   "loc": "Nob Hill",         "win": (t(15,15), t(19,15)), "min_dur": 105},
    {"name": "Brian",     "loc": "Marina District",  "win": (t(14,15), t(22,0)),  "min_dur": 30},
    {"name": "Emily",     "loc": "Pacific Heights",  "win": (t(11,15), t(19,45)), "min_dur": 15},
    {"name": "Karen",     "loc": "Haight-Ashbury",   "win": (t(11,45), t(17,30)), "min_dur": 30},
    {"name": "Stephanie", "loc": "Mission District", "win": (t(13,0),  t(15,45)), "min_dur": 75},
    {"name": "James",     "loc": "Chinatown",        "win": (t(14,30), t(19,0)),  "min_dur": 120},
    {"name": "Steven",    "loc": "Russian Hill",     "win": (t(14,0),  t(20,0)),  "min_dur": 30},
    {"name": "Elizabeth", "loc": "Alamo Square",     "win": (t(13,0),  t(17,15)), "min_dur": 120},
    {"name": "William",   "loc": "Bayview",          "win": (t(18,15), t(20,15)), "min_dur": 90},
]

n = len(friends)

# Z3 variables
meet = [Bool(f"meet_{i}") for i in range(n)]
start = [Int(f"start_{i}") for i in range(n)]
end   = [Int(f"end_{i}") for i in range(n)]

# Pairwise ordering booleans
before = [[None]*n for _ in range(n)]
for i in range(n):
    for j in range(n):
        if i != j:
            before[i][j] = Bool(f"before_{i}_{j}")

opt = Optimize()

# Constraints per friend
for i, f in enumerate(friends):
    win_start, win_end = f["win"]
    dur = f["min_dur"]

    # Meeting window and duration if meeting
    opt.add(Implies(meet[i], And(start[i] >= win_start,
                                 end[i] == start[i] + dur,
                                 end[i] <= win_end)))
    # If not meeting, tie start and end (no duration)
    opt.add(Implies(Not(meet[i]), end[i] == start[i]))

    # Must be reachable from the start location at 09:00 (conservative lower bound)
    # start[i] >= START_TIME + travel(START_LOC -> f["loc"]) if meet[i]
    opt.add(Implies(meet[i], start[i] >= START_TIME + T[START_LOC][f["loc"]]))

# Disjunctive sequencing with travel times
for i in range(n):
    for j in range(i+1, n):
        li = friends[i]["loc"]
        lj = friends[j]["loc"]
        ti2j = T[li][lj]
        tj2i = T[lj][li]
        # If both meetings happen, either i before j with travel, or j before i with travel
        opt.add(Implies(And(meet[i], meet[j], before[i][j]),
                        end[i] + ti2j <= start[j]))
        opt.add(Implies(And(meet[i], meet[j], Not(before[i][j])),
                        end[j] + tj2i <= start[i]))
        # Symmetry helper: if i before j then not j before i, but not strictly necessary due to time constraints.
        # We won't add equivalence to keep the model simple.

# Objective: maximize number of meetings
total_meetings = Sum([If(meet[i], 1, 0) for i in range(n)])
h1 = opt.maximize(total_meetings)

# Secondary objective: maximize total meeting time (ties broken in favor of longer total duration)
total_meeting_minutes = Sum([If(meet[i], friends[i]["min_dur"], 0) for i in range(n)])
h2 = opt.maximize(total_meeting_minutes)

# Solve
if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
    raise SystemExit

m = opt.model()

# Extract chosen meetings and times
chosen = []
for i, f in enumerate(friends):
    if m.evaluate(meet[i], model_completion=True) == True:
        s = m.evaluate(start[i], model_completion=True).as_long()
        e = m.evaluate(end[i], model_completion=True).as_long()
        chosen.append((s, {
            "action": "meet",
            "person": f["name"],
            "start_time": minutes_to_hhmm(s),
            "end_time": minutes_to_hhmm(e)
        }))

# Sort by start time
chosen.sort(key=lambda x: x[0])
itinerary = [entry for _, entry in chosen]

print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))