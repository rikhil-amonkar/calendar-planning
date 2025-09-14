import json
from z3 import *

# Helper functions
def time_to_minutes(t):
    # t like '10:15' or '9:00' 24-hour
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel time matrix (minutes)
dist = {
    "Presidio": {
        "Fisherman's Wharf": 19,
        "Alamo Square": 19,
        "Financial District": 23,
        "Union Square": 22,
        "Sunset District": 15,
        "Embarcadero": 20,
        "Golden Gate Park": 12,
        "Chinatown": 21,
        "Richmond District": 7,
    },
    "Fisherman's Wharf": {
        "Presidio": 17,
        "Alamo Square": 21,
        "Financial District": 11,
        "Union Square": 13,
        "Sunset District": 27,
        "Embarcadero": 8,
        "Golden Gate Park": 25,
        "Chinatown": 12,
        "Richmond District": 18,
    },
    "Alamo Square": {
        "Presidio": 17,
        "Fisherman's Wharf": 19,
        "Financial District": 17,
        "Union Square": 14,
        "Sunset District": 16,
        "Embarcadero": 16,
        "Golden Gate Park": 9,
        "Chinatown": 15,
        "Richmond District": 11,
    },
    "Financial District": {
        "Presidio": 22,
        "Fisherman's Wharf": 10,
        "Alamo Square": 17,
        "Union Square": 9,
        "Sunset District": 30,
        "Embarcadero": 4,
        "Golden Gate Park": 23,
        "Chinatown": 5,
        "Richmond District": 21,
    },
    "Union Square": {
        "Presidio": 24,
        "Fisherman's Wharf": 15,
        "Alamo Square": 15,
        "Financial District": 9,
        "Sunset District": 27,
        "Embarcadero": 11,
        "Golden Gate Park": 22,
        "Chinatown": 7,
        "Richmond District": 20,
    },
    "Sunset District": {
        "Presidio": 16,
        "Fisherman's Wharf": 29,
        "Alamo Square": 17,
        "Financial District": 30,
        "Union Square": 30,
        "Embarcadero": 30,
        "Golden Gate Park": 11,
        "Chinatown": 30,
        "Richmond District": 12,
    },
    "Embarcadero": {
        "Presidio": 20,
        "Fisherman's Wharf": 6,
        "Alamo Square": 19,
        "Financial District": 5,
        "Union Square": 10,
        "Sunset District": 30,
        "Golden Gate Park": 25,
        "Chinatown": 7,
        "Richmond District": 21,
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Fisherman's Wharf": 24,
        "Alamo Square": 9,
        "Financial District": 26,
        "Union Square": 22,
        "Sunset District": 10,
        "Embarcadero": 25,
        "Chinatown": 23,
        "Richmond District": 7,
    },
    "Chinatown": {
        "Presidio": 19,
        "Fisherman's Wharf": 8,
        "Alamo Square": 17,
        "Financial District": 5,
        "Union Square": 7,
        "Sunset District": 29,
        "Embarcadero": 5,
        "Golden Gate Park": 23,
        "Richmond District": 20,
    },
    "Richmond District": {
        "Presidio": 7,
        "Fisherman's Wharf": 18,
        "Alamo Square": 13,
        "Financial District": 22,
        "Union Square": 21,
        "Sunset District": 11,
        "Embarcadero": 19,
        "Golden Gate Park": 9,
        "Chinatown": 20,
    },
}

# Participants with constraints
people = [
    {"name": "Jeffrey",   "location": "Fisherman's Wharf", "start": "10:15", "end": "13:00", "min_dur": 90},
    {"name": "Ronald",    "location": "Alamo Square",      "start": "7:45",  "end": "14:45", "min_dur": 120},
    {"name": "Jason",     "location": "Financial District", "start": "10:45","end": "16:00", "min_dur": 105},
    {"name": "Melissa",   "location": "Union Square",      "start": "17:45", "end": "18:15", "min_dur": 15},
    {"name": "Elizabeth", "location": "Sunset District",    "start": "14:45","end": "17:30", "min_dur": 105},
    {"name": "Margaret",  "location": "Embarcadero",       "start": "13:15", "end": "19:00", "min_dur": 90},
    {"name": "George",    "location": "Golden Gate Park",  "start": "19:00", "end": "22:00", "min_dur": 75},
    {"name": "Richard",   "location": "Chinatown",         "start": "9:30",  "end": "21:00", "min_dur": 15},
    {"name": "Laura",     "location": "Richmond District", "start": "9:45",  "end": "18:00", "min_dur": 60},
]

# Preprocess times
for p in people:
    p["start_min"] = time_to_minutes(p["start"])
    p["end_min"] = time_to_minutes(p["end"])

# Start location/time
START_LOC = "Presidio"
START_TIME = time_to_minutes("9:00")

N = len(people)

# Z3 variables
opt = Optimize()

attend = [Bool(f"attend_{i}") for i in range(N)]
t = [Int(f"start_{i}") for i in range(N)]
dur = [IntVal(people[i]["min_dur"]) for i in range(N)]

# y[i][j] = True if meeting i is immediately followed by j in the route
y = [[Bool(f"y_{i}_{j}") if i != j else BoolVal(False) for j in range(N)] for i in range(N)]
# s[i] = True if the route starts at meeting i
s = [Bool(f"s_{i}") for i in range(N)]

# Constraints
for i in range(N):
    # Time window if attended
    a_i = people[i]["start_min"]
    b_i = people[i]["end_min"]
    d_i = people[i]["min_dur"]
    opt.add(Implies(attend[i], And(t[i] >= a_i, t[i] + d_i <= b_i)))
    # If start edge chosen, must attend
    opt.add(Implies(s[i], attend[i]))

# For all edges y[i][j], if chosen then both meetings are attended
for i in range(N):
    for j in range(N):
        if i == j:
            continue
        opt.add(Implies(y[i][j], And(attend[i], attend[j])))

# Predecessor constraints: each attended meeting has exactly one predecessor (either START or another meeting)
for i in range(N):
    incoming_sum = Sum([If(s[i], 1, 0)] + [If(y[j][i], 1, 0) for j in range(N) if j != i])
    opt.add(incoming_sum == If(attend[i], 1, 0))

# Outgoing constraints: each attended meeting has at most one outgoing
outgoing_sums = []
for i in range(N):
    out_i = Sum([If(y[i][j], 1, 0) for j in range(N) if j != i])
    outgoing_sums.append(out_i)
    opt.add(out_i <= If(attend[i], 1, 0))

# Count of attended meetings
n_attended = Int("n_attended")
opt.add(n_attended == Sum([If(attend[i], 1, 0) for i in range(N)]))

# Exactly one start arc if there is at least one meeting, else none
S_out = Sum([If(s[i], 1, 0) for i in range(N)])
opt.add(If(n_attended == 0, S_out == 0, S_out == 1))

# Total number of internal edges equals n_attended - 1 if any attended, else 0
total_internal_edges = Sum([If(y[i][j], 1, 0) for i in range(N) for j in range(N) if i != j])
opt.add(total_internal_edges == If(n_attended == 0, 0, n_attended - 1))

# Time feasibility constraints along edges
# From START to first
for i in range(N):
    travel_si = dist[START_LOC][people[i]["location"]]
    opt.add(Implies(s[i], t[i] >= START_TIME + travel_si))

# Between meetings along an edge
for i in range(N):
    for j in range(N):
        if i == j: 
            continue
        travel_ij = dist[people[i]["location"]][people[j]["location"]]
        d_i = people[i]["min_dur"]
        opt.add(Implies(y[i][j], t[j] >= t[i] + d_i + travel_ij))

# "Last" meeting detection and finish time (to break ties by earliest finish)
M = 2000
last = [Bool(f"last_{i}") for i in range(N)]
for i in range(N):
    out_i = outgoing_sums[i]
    # last_i <-> (attend_i and out_i == 0)
    opt.add(Implies(last[i], And(attend[i], out_i == 0)))
    opt.add(Implies(And(attend[i], out_i == 0), last[i]))

sum_last = Sum([If(last[i], 1, 0) for i in range(N)])
opt.add(If(n_attended == 0, sum_last == 0, sum_last == 1))

finish = Int("finish")
opt.add(finish >= 0, finish <= 24 * 60)
for i in range(N):
    d_i = people[i]["min_dur"]
    bi = If(last[i], 1, 0)
    opt.add(finish >= t[i] + d_i - M * (1 - bi))
    opt.add(finish <= t[i] + d_i + M * (1 - bi))

# Objective: maximize number of meetings; tie-breaker minimize finish time
opt.maximize(n_attended)
opt.minimize(finish)

# Solve
res = opt.check()
itinerary = []

if res == sat:
    model = opt.model()
    # Reconstruct route
    # Find the start meeting
    idx_start = None
    for i in range(N):
        if is_true(model.evaluate(s[i])):
            idx_start = i
            break

    order = []
    if idx_start is not None:
        curr = idx_start
        visited = set()
        while curr is not None and curr not in visited:
            visited.add(curr)
            if is_true(model.evaluate(attend[curr])):
                start_min = model.evaluate(t[curr]).as_long()
                end_min = start_min + people[curr]["min_dur"]
                itinerary.append({
                    "action": "meet",
                    "location": people[curr]["location"],
                    "person": people[curr]["name"],
                    "start_time": minutes_to_str(start_min),
                    "end_time": minutes_to_str(end_min)
                })
            # Move to next via y[curr][j]
            next_idx = None
            for j in range(N):
                if curr != j and is_true(model.evaluate(y[curr][j])):
                    next_idx = j
                    break
            curr = next_idx

# Output JSON
output = {
    "itinerary": itinerary
}

print(json.dumps(output, ensure_ascii=False, indent=2))