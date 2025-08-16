# pip install z3-solver
from z3 import Optimize, Int, Bool, If, And, Or, Implies, sat
import json

# Time helpers
def to_min(hhmm):
    hh, mm = map(int, hhmm.split(":"))
    return hh * 60 + mm

def to_hhmm(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Data
locations = ["Bayview", "North Beach", "Presidio", "Haight-Ashbury", "Union Square"]

# Directed travel times (minutes)
T = {
    "Bayview": {
        "Bayview": 0, "North Beach": 21, "Presidio": 31, "Haight-Ashbury": 19, "Union Square": 17
    },
    "North Beach": {
        "Bayview": 22, "North Beach": 0, "Presidio": 17, "Haight-Ashbury": 18, "Union Square": 7
    },
    "Presidio": {
        "Bayview": 31, "North Beach": 18, "Presidio": 0, "Haight-Ashbury": 15, "Union Square": 22
    },
    "Haight-Ashbury": {
        "Bayview": 18, "North Beach": 19, "Presidio": 15, "Haight-Ashbury": 0, "Union Square": 17
    },
    "Union Square": {
        "Bayview": 15, "North Beach": 10, "Presidio": 24, "Haight-Ashbury": 18, "Union Square": 0
    },
}

start_loc = "Bayview"
start_time = to_min("09:00")

friends = {
    "Barbara": {
        "location": "North Beach",
        "avail_start": to_min("13:45"),
        "avail_end": to_min("20:15"),
        "min_dur": 60
    },
    "Margaret": {
        "location": "Presidio",
        "avail_start": to_min("10:15"),
        "avail_end": to_min("15:15"),
        "min_dur": 30
    },
    "Kevin": {
        "location": "Haight-Ashbury",
        "avail_start": to_min("20:00"),
        "avail_end": to_min("20:45"),
        "min_dur": 30
    },
    "Kimberly": {
        "location": "Union Square",
        "avail_start": to_min("07:45"),
        "avail_end": to_min("16:45"),
        "min_dur": 30
    },
}

# Z3 model
opt = Optimize()

# Variables per friend
s = {}    # start time (minutes from midnight)
attend = {}  # Bool attend
dur = {}  # fixed duration equal to minimum required for simplicity
loc = {}  # location name for quick access
avail_start = {}
avail_end = {}
base_arrival = {}

for name, info in friends.items():
    s[name] = Int(f"s_{name}")
    attend[name] = Bool(f"attend_{name}")
    dur[name] = info["min_dur"]
    loc[name] = info["location"]
    avail_start[name] = info["avail_start"]
    avail_end[name] = info["avail_end"]
    base_arrival[name] = start_time + T[start_loc][loc[name]]

    # Window constraints and base arrival feasibility if attending
    opt.add(Implies(attend[name],
                    And(
                        s[name] >= avail_start[name],
                        s[name] + dur[name] <= avail_end[name],
                        s[name] >= base_arrival[name]
                    )))

# Pairwise disjunctive scheduling with travel time
names = list(friends.keys())
for i in range(len(names)):
    for j in range(i + 1, len(names)):
        ni, nj = names[i], names[j]
        ti_j = T[loc[ni]][loc[nj]]
        tj_i = T[loc[nj]][loc[ni]]
        # If attending both, either i before j (with travel) or j before i (with travel)
        opt.add(Implies(And(attend[ni], attend[nj]),
                        Or(s[ni] + dur[ni] + ti_j <= s[nj],
                           s[nj] + dur[nj] + tj_i <= s[ni])))

# Objective 1: maximize number of friends met
count = sum([If(attend[n], 1, 0) for n in names])
opt.maximize(count)

# Objective 2: minimize makespan (latest end time among attended meetings)
M = Int("makespan")
# makespan lower bound
opt.add(M >= start_time)
for n in names:
    # If attending n, its end time must be <= M
    opt.add(Implies(attend[n], s[n] + dur[n] <= M))
opt.minimize(M)

# Optionally, nudge starts earlier to get "cleaner" times
# e.g., minimize the sum of start times (not essential)
opt.minimize(sum([If(attend[n], s[n], start_time) for n in names]))

# Solve
if opt.check() != sat:
    raise RuntimeError("No feasible schedule found")

model = opt.model()

# Build itinerary JSON from model
itinerary = []
for n in names:
    if model.eval(attend[n], model_completion=True):
        start_min = model.eval(s[n]).as_long()
        end_min = start_min + dur[n]
        itinerary.append({
            "action": "meet",
            "person": n,
            "start_time": to_hhmm(start_min),
            "end_time": to_hhmm(end_min)
        })

# Sort by start_time
itinerary.sort(key=lambda x: to_min(x["start_time"]))

# Print JSON
print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))