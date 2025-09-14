import json
import sys
from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, is_true, Implies, sat

# Helper functions
def parse_time(tstr):
    # tstr like '9:00', '18:30' 24-hour without leading zero requirement
    h, m = tstr.split(':')
    return int(h) * 60 + int(m)

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times (minutes) between neighborhoods
locations = [
    "Pacific Heights", "Marina District", "The Castro", "Richmond District",
    "Alamo Square", "Financial District", "Presidio", "Mission District",
    "Nob Hill", "Russian Hill"
]

# Initialize travel times
travel = {a: {b: None for b in locations} for a in locations}
def set_travel(a, b, t):
    travel[a][b] = t

# Given travel times
set_travel("Pacific Heights", "Marina District", 6)
set_travel("Pacific Heights", "The Castro", 16)
set_travel("Pacific Heights", "Richmond District", 12)
set_travel("Pacific Heights", "Alamo Square", 10)
set_travel("Pacific Heights", "Financial District", 13)
set_travel("Pacific Heights", "Presidio", 11)
set_travel("Pacific Heights", "Mission District", 15)
set_travel("Pacific Heights", "Nob Hill", 8)
set_travel("Pacific Heights", "Russian Hill", 7)

set_travel("Marina District", "Pacific Heights", 7)
set_travel("Marina District", "The Castro", 22)
set_travel("Marina District", "Richmond District", 11)
set_travel("Marina District", "Alamo Square", 15)
set_travel("Marina District", "Financial District", 17)
set_travel("Marina District", "Presidio", 10)
set_travel("Marina District", "Mission District", 20)
set_travel("Marina District", "Nob Hill", 12)
set_travel("Marina District", "Russian Hill", 8)

set_travel("The Castro", "Pacific Heights", 16)
set_travel("The Castro", "Marina District", 21)
set_travel("The Castro", "Richmond District", 16)
set_travel("The Castro", "Alamo Square", 8)
set_travel("The Castro", "Financial District", 21)
set_travel("The Castro", "Presidio", 20)
set_travel("The Castro", "Mission District", 7)
set_travel("The Castro", "Nob Hill", 16)
set_travel("The Castro", "Russian Hill", 18)

set_travel("Richmond District", "Pacific Heights", 10)
set_travel("Richmond District", "Marina District", 9)
set_travel("Richmond District", "The Castro", 16)
set_travel("Richmond District", "Alamo Square", 13)
set_travel("Richmond District", "Financial District", 22)
set_travel("Richmond District", "Presidio", 7)
set_travel("Richmond District", "Mission District", 20)
set_travel("Richmond District", "Nob Hill", 17)
set_travel("Richmond District", "Russian Hill", 13)

set_travel("Alamo Square", "Pacific Heights", 10)
set_travel("Alamo Square", "Marina District", 15)
set_travel("Alamo Square", "The Castro", 8)
set_travel("Alamo Square", "Richmond District", 11)
set_travel("Alamo Square", "Financial District", 17)
set_travel("Alamo Square", "Presidio", 17)
set_travel("Alamo Square", "Mission District", 10)
set_travel("Alamo Square", "Nob Hill", 11)
set_travel("Alamo Square", "Russian Hill", 13)

set_travel("Financial District", "Pacific Heights", 13)
set_travel("Financial District", "Marina District", 15)
set_travel("Financial District", "The Castro", 20)
set_travel("Financial District", "Richmond District", 21)
set_travel("Financial District", "Alamo Square", 17)
set_travel("Financial District", "Presidio", 22)
set_travel("Financial District", "Mission District", 17)
set_travel("Financial District", "Nob Hill", 8)
set_travel("Financial District", "Russian Hill", 11)

set_travel("Presidio", "Pacific Heights", 11)
set_travel("Presidio", "Marina District", 11)
set_travel("Presidio", "The Castro", 21)
set_travel("Presidio", "Richmond District", 7)
set_travel("Presidio", "Alamo Square", 19)
set_travel("Presidio", "Financial District", 23)
set_travel("Presidio", "Mission District", 26)
set_travel("Presidio", "Nob Hill", 18)
set_travel("Presidio", "Russian Hill", 14)

set_travel("Mission District", "Pacific Heights", 16)
set_travel("Mission District", "Marina District", 19)
set_travel("Mission District", "The Castro", 7)
set_travel("Mission District", "Richmond District", 20)
set_travel("Mission District", "Alamo Square", 11)
set_travel("Mission District", "Financial District", 15)
set_travel("Mission District", "Presidio", 25)
set_travel("Mission District", "Nob Hill", 12)
set_travel("Mission District", "Russian Hill", 15)

set_travel("Nob Hill", "Pacific Heights", 8)
set_travel("Nob Hill", "Marina District", 11)
set_travel("Nob Hill", "The Castro", 17)
set_travel("Nob Hill", "Richmond District", 14)
set_travel("Nob Hill", "Alamo Square", 11)
set_travel("Nob Hill", "Financial District", 9)
set_travel("Nob Hill", "Presidio", 17)
set_travel("Nob Hill", "Mission District", 13)
set_travel("Nob Hill", "Russian Hill", 5)

set_travel("Russian Hill", "Pacific Heights", 7)
set_travel("Russian Hill", "Marina District", 7)
set_travel("Russian Hill", "The Castro", 21)
set_travel("Russian Hill", "Richmond District", 14)
set_travel("Russian Hill", "Alamo Square", 15)
set_travel("Russian Hill", "Financial District", 11)
set_travel("Russian Hill", "Presidio", 14)
set_travel("Russian Hill", "Mission District", 16)
set_travel("Russian Hill", "Nob Hill", 5)

# Set zero for self-travel
for a in locations:
    set_travel(a, a, 0)

# Participants and their constraints
participants = [
    {"name": "Linda",   "location": "Marina District",   "start": "18:00", "end": "22:00", "min_duration": 30},
    {"name": "Kenneth", "location": "The Castro",        "start": "14:45", "end": "16:15", "min_duration": 30},
    {"name": "Kimberly","location": "Richmond District", "start": "14:15", "end": "22:00", "min_duration": 30},
    {"name": "Paul",    "location": "Alamo Square",      "start": "21:00", "end": "21:30", "min_duration": 15},
    {"name": "Carol",   "location": "Financial District","start": "10:15", "end": "12:00", "min_duration": 60},
    {"name": "Brian",   "location": "Presidio",          "start": "10:00", "end": "21:30", "min_duration": 75},
    {"name": "Laura",   "location": "Mission District",  "start": "16:15", "end": "20:30", "min_duration": 30},
    {"name": "Sandra",  "location": "Nob Hill",          "start": "9:15",  "end": "18:30", "min_duration": 60},
    {"name": "Karen",   "location": "Russian Hill",      "start": "18:30", "end": "22:00", "min_duration": 75},
]

# Convert times to minutes
for p in participants:
    p["start_min"] = parse_time(p["start"])
    p["end_min"] = parse_time(p["end"])

# Initial arrival
home_location = "Pacific Heights"
arrival_time = parse_time("9:00")

# Build SMT model
opt = Optimize()

# Variables
start_vars = {}
end_vars = {}
met_vars = {}
duration = {}

for p in participants:
    pname = p["name"]
    start_vars[pname] = Int(f"start_{pname}")
    end_vars[pname] = Int(f"end_{pname}")
    met_vars[pname] = Bool(f"met_{pname}")
    duration[pname] = p["min_duration"]

    # Domain constraints when met
    opt.add(Implies(met_vars[pname], start_vars[pname] >= p["start_min"]))
    opt.add(Implies(met_vars[pname], end_vars[pname] <= p["end_min"]))
    opt.add(Implies(met_vars[pname], end_vars[pname] == start_vars[pname] + duration[pname]))
    # Feasibility from initial arrival
    opt.add(Implies(met_vars[pname], start_vars[pname] >= arrival_time + travel[home_location][p["location"]]))
    # Keep times within day bounds if met
    opt.add(Implies(met_vars[pname], And(start_vars[pname] >= parse_time("9:00"), end_vars[pname] <= parse_time("22:00"))))

# Pairwise ordering constraints with travel times
before_vars = {}
for i in range(len(participants)):
    for j in range(i+1, len(participants)):
        pi = participants[i]
        pj = participants[j]
        ni = pi["name"]
        nj = pj["name"]
        li = pi["location"]
        lj = pj["location"]
        b = Bool(f"before_{ni}_{nj}")
        before_vars[(ni, nj)] = b
        # If both are met, they must be ordered with travel time buffer
        opt.add(Implies(And(met_vars[ni], met_vars[nj], b),
                        end_vars[ni] + travel[li][lj] <= start_vars[nj]))
        opt.add(Implies(And(met_vars[ni], met_vars[nj], Not(b)),
                        end_vars[nj] + travel[lj][li] <= start_vars[ni]))

# Objective: maximize number of meetings
total_meetings = Sum([If(met_vars[p["name"]], 1, 0) for p in participants])
opt.maximize(total_meetings)

# Optional tie-breakers: minimize the latest end time among scheduled meetings
latest_end = Int("latest_end")
opt.add(latest_end >= arrival_time)
for p in participants:
    opt.add(Implies(met_vars[p["name"]], latest_end >= end_vars[p["name"]]))
opt.minimize(latest_end)

# Solve
res = opt.check()
if res != sat:
    print(json.dumps({"itinerary": []}))
    sys.exit(0)

model = opt.model()

# Extract results
schedule = []
for p in participants:
    pname = p["name"]
    if is_true(model.eval(met_vars[pname])):
        s = model.eval(start_vars[pname]).as_long()
        e = model.eval(end_vars[pname]).as_long()
        schedule.append({
            "person": pname,
            "location": p["location"],
            "start": s,
            "end": e
        })

# Sort by start time
schedule.sort(key=lambda x: x["start"])

# Build JSON itinerary
itinerary = []
for item in schedule:
    itinerary.append({
        "action": "meet",
        "location": item["location"],
        "person": item["person"],
        "start_time": minutes_to_str(item["start"]),
        "end_time": minutes_to_str(item["end"])
    })

print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))