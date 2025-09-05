import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Locations and travel times (directed, minutes)
travel = {
    'Marina District': {
        'Embarcadero': 14, 'Bayview': 27, 'Union Square': 16, 'Chinatown': 15,
        'Sunset District': 19, 'Golden Gate Park': 18, 'Financial District': 17,
        'Haight-Ashbury': 16, 'Mission District': 20
    },
    'Embarcadero': {
        'Marina District': 12, 'Bayview': 21, 'Union Square': 10, 'Chinatown': 7,
        'Sunset District': 30, 'Golden Gate Park': 25, 'Financial District': 5,
        'Haight-Ashbury': 21, 'Mission District': 20
    },
    'Bayview': {
        'Marina District': 27, 'Embarcadero': 19, 'Union Square': 18, 'Chinatown': 19,
        'Sunset District': 23, 'Golden Gate Park': 22, 'Financial District': 19,
        'Haight-Ashbury': 19, 'Mission District': 13
    },
    'Union Square': {
        'Marina District': 18, 'Embarcadero': 11, 'Bayview': 15, 'Chinatown': 7,
        'Sunset District': 27, 'Golden Gate Park': 22, 'Financial District': 9,
        'Haight-Ashbury': 18, 'Mission District': 14
    },
    'Chinatown': {
        'Marina District': 12, 'Embarcadero': 5, 'Bayview': 20, 'Union Square': 7,
        'Sunset District': 29, 'Golden Gate Park': 23, 'Financial District': 5,
        'Haight-Ashbury': 19, 'Mission District': 17
    },
    'Sunset District': {
        'Marina District': 21, 'Embarcadero': 30, 'Bayview': 22, 'Union Square': 30,
        'Chinatown': 30, 'Golden Gate Park': 11, 'Financial District': 30,
        'Haight-Ashbury': 15, 'Mission District': 25
    },
    'Golden Gate Park': {
        'Marina District': 16, 'Embarcadero': 25, 'Bayview': 23, 'Union Square': 22,
        'Chinatown': 23, 'Sunset District': 10, 'Financial District': 26,
        'Haight-Ashbury': 7, 'Mission District': 17
    },
    'Financial District': {
        'Marina District': 15, 'Embarcadero': 4, 'Bayview': 19, 'Union Square': 9,
        'Chinatown': 5, 'Sunset District': 30, 'Golden Gate Park': 23,
        'Haight-Ashbury': 19, 'Mission District': 17
    },
    'Haight-Ashbury': {
        'Marina District': 17, 'Embarcadero': 20, 'Bayview': 18, 'Union Square': 19,
        'Chinatown': 19, 'Sunset District': 15, 'Golden Gate Park': 7,
        'Financial District': 21, 'Mission District': 11
    },
    'Mission District': {
        'Marina District': 19, 'Embarcadero': 19, 'Bayview': 14, 'Union Square': 15,
        'Chinatown': 16, 'Sunset District': 24, 'Golden Gate Park': 17,
        'Financial District': 15, 'Haight-Ashbury': 12
    }
}

# People and constraints
people = [
    {"name": "Joshua",   "location": "Embarcadero",      "start": minutes(9,45),  "end": minutes(18,0),  "min": 105},
    {"name": "Jeffrey",  "location": "Bayview",          "start": minutes(9,45),  "end": minutes(20,15), "min": 75},
    {"name": "Charles",  "location": "Union Square",     "start": minutes(10,45), "end": minutes(20,15), "min": 120},
    {"name": "Joseph",   "location": "Chinatown",        "start": minutes(7,0),   "end": minutes(15,30), "min": 60},
    {"name": "Elizabeth","location": "Sunset District",  "start": minutes(9,0),   "end": minutes(9,45),  "min": 45},
    {"name": "Matthew",  "location": "Golden Gate Park", "start": minutes(11,0),  "end": minutes(19,30), "min": 45},
    {"name": "Carol",    "location": "Financial District","start": minutes(10,45),"end": minutes(11,15), "min": 15},
    {"name": "Paul",     "location": "Haight-Ashbury",   "start": minutes(19,15), "end": minutes(20,30), "min": 15},
    {"name": "Rebecca",  "location": "Mission District", "start": minutes(17,0),  "end": minutes(21,45), "min": 45},
]
num_people = len(people)

# Helper arrays for Z3 selection
loc_names = [p["location"] for p in people]
avail_start = [p["start"] for p in people]
avail_end = [p["end"] for p in people]
min_durs = [p["min"] for p in people]

# Build start travel and travel matrix aligned to people indices
start_location = "Marina District"
start_time = minutes(9,0)

start_travel = [travel[start_location][loc_names[i]] for i in range(num_people)]
travel_matrix = [[travel[loc_names[i]][loc_names[j]] for j in range(num_people)] for i in range(num_people)]

# Helper functions to select piecewise values based on index variables
def pick1(vals, idx):
    # vals: list of Int constants (python ints); idx: z3 Int
    expr = IntVal(vals[0])
    for i in range(1, len(vals)):
        expr = If(idx == i, IntVal(vals[i]), expr)
    return expr

def pick2(mat, idx_i, idx_j):
    # mat: list of list of ints
    row_expr = None
    for i in range(len(mat)):
        inner = IntVal(mat[i][0])
        for j in range(1, len(mat[i])):
            inner = If(idx_j == j, IntVal(mat[i][j]), inner)
        row_expr = inner if row_expr is None else If(idx_i == i, inner, row_expr)
    return row_expr

# Z3 model
opt = Optimize()

max_steps = num_people  # at most one meeting per person
used = [Bool(f"used_{k}") for k in range(max_steps)]
pidx = [Int(f"pidx_{k}") for k in range(max_steps)]
s = [Int(f"s_{k}") for k in range(max_steps)]
e = [Int(f"e_{k}") for k in range(max_steps)]

DAY_MAX = minutes(23,59)  # for bounding

# Contiguity of used steps and domains
for k in range(max_steps):
    # Domain of pidx depending on used
    opt.add(Implies(used[k], And(pidx[k] >= 0, pidx[k] < num_people)))
    opt.add(Implies(Not(used[k]), pidx[k] == -1))
    # Time bounds
    opt.add(And(s[k] >= 0, s[k] <= DAY_MAX))
    opt.add(And(e[k] >= 0, e[k] <= DAY_MAX))
    # Meeting window and min duration when used
    opt.add(Implies(used[k], s[k] >= pick1(avail_start, pidx[k])))
    opt.add(Implies(used[k], e[k] <= pick1(avail_end, pidx[k])))
    opt.add(Implies(used[k], e[k] - s[k] >= pick1(min_durs, pidx[k])))

# Ensure steps are contiguous from the start (no gaps)
for k in range(1, max_steps):
    opt.add(Implies(used[k], used[k-1]))

# No duplicate people across used steps
for i in range(max_steps):
    for j in range(i+1, max_steps):
        opt.add(Implies(And(used[i], used[j]), pidx[i] != pidx[j]))

# Travel and sequencing constraints
# First used step must be reachable from the start location at 9:00
opt.add(Implies(used[0], s[0] >= start_time + pick1(start_travel, pidx[0])))

# Consecutive steps: time must include travel between locations
for k in range(max_steps - 1):
    opt.add(Implies(used[k+1], s[k+1] >= e[k] + pick2(travel_matrix, pidx[k], pidx[k+1])))

# Additionally enforce non-decreasing times if used (helps the solver)
for k in range(max_steps - 1):
    opt.add(Implies(used[k+1], s[k+1] >= s[k]))

# Objective: maximize number of meetings
num_meetings = Sum([If(used[k], 1, 0) for k in range(max_steps)])
opt.maximize(num_meetings)

# Optional secondary objective: maximize total meeting time (ties broken)
total_meeting_minutes = Sum([If(used[k], e[k] - s[k], 0) for k in range(max_steps)])
opt.maximize(total_meeting_minutes)

# Solve
result = opt.check()
itinerary = []

if result == sat:
    model = opt.model()
    # Collect used steps in order
    for k in range(max_steps):
        if is_true(model.eval(used[k], model_completion=True)):
            idx = model.eval(pidx[k], model_completion=True).as_long()
            start_min = model.eval(s[k], model_completion=True).as_long()
            end_min = model.eval(e[k], model_completion=True).as_long()
            itinerary.append({
                "action": "meet",
                "location": people[idx]["location"],
                "person": people[idx]["name"],
                "start_time": fmt_time(start_min),
                "end_time": fmt_time(end_min)
            })
        else:
            break

output = {
    "itinerary": itinerary
}

print(json.dumps(output, ensure_ascii=False))