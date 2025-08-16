# Requires: z3-solver (pip install z3-solver)

from z3 import Optimize, Int, Bool, If, Or, And, Not, Sum
import json

def to_minutes(t):
    hh, mm = map(int, t.split(":"))
    return hh * 60 + mm

def to_hhmm(m):
    return f"{m//60:02d}:{m%60:02d}"

# Data
start_location = "Pacific Heights"
start_time_str = "09:00"
start_time = to_minutes(start_time_str)

people = [
    # name, location, window_start, window_end, min_duration
    ("Helen", "Golden Gate Park", "09:30", "12:15", 45),
    ("Steven", "The Castro", "20:15", "22:00", 105),
    ("Deborah", "Bayview", "08:30", "12:00", 30),
    ("Matthew", "Marina District", "09:15", "14:15", 45),
    ("Joseph", "Union Square", "14:15", "18:45", 120),
    ("Ronald", "Sunset District", "16:00", "20:45", 60),
    ("Robert", "Alamo Square", "18:30", "21:15", 120),
    ("Rebecca", "Financial District", "14:45", "16:15", 30),
    ("Elizabeth", "Mission District", "18:30", "21:00", 120),
]

# Convert windows to minutes
people_data = []
for name, loc, ws, we, dur in people:
    people_data.append({
        "name": name,
        "location": loc,
        "win_start": to_minutes(ws),
        "win_end": to_minutes(we),
        "min_dur": dur
    })

# Travel times (minutes) as given
travel = {
    "Pacific Heights": {
        "Golden Gate Park": 15,
        "The Castro": 16,
        "Bayview": 22,
        "Marina District": 6,
        "Union Square": 12,
        "Sunset District": 21,
        "Alamo Square": 10,
        "Financial District": 13,
        "Mission District": 15
    },
    "Golden Gate Park": {
        "Pacific Heights": 16,
        "The Castro": 13,
        "Bayview": 23,
        "Marina District": 16,
        "Union Square": 22,
        "Sunset District": 10,
        "Alamo Square": 9,
        "Financial District": 26,
        "Mission District": 17
    },
    "The Castro": {
        "Pacific Heights": 16,
        "Golden Gate Park": 11,
        "Bayview": 19,
        "Marina District": 21,
        "Union Square": 19,
        "Sunset District": 17,
        "Alamo Square": 8,
        "Financial District": 21,
        "Mission District": 7
    },
    "Bayview": {
        "Pacific Heights": 23,
        "Golden Gate Park": 22,
        "The Castro": 19,
        "Marina District": 27,
        "Union Square": 18,
        "Sunset District": 23,
        "Alamo Square": 16,
        "Financial District": 19,
        "Mission District": 13
    },
    "Marina District": {
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
        "The Castro": 22,
        "Bayview": 27,
        "Union Square": 16,
        "Sunset District": 19,
        "Alamo Square": 15,
        "Financial District": 17,
        "Mission District": 20
    },
    "Union Square": {
        "Pacific Heights": 15,
        "Golden Gate Park": 22,
        "The Castro": 17,
        "Bayview": 15,
        "Marina District": 18,
        "Sunset District": 27,
        "Alamo Square": 15,
        "Financial District": 9,
        "Mission District": 14
    },
    "Sunset District": {
        "Pacific Heights": 21,
        "Golden Gate Park": 11,
        "The Castro": 17,
        "Bayview": 22,
        "Marina District": 21,
        "Union Square": 30,
        "Alamo Square": 17,
        "Financial District": 30,
        "Mission District": 25
    },
    "Alamo Square": {
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "The Castro": 8,
        "Bayview": 16,
        "Marina District": 15,
        "Union Square": 14,
        "Sunset District": 16,
        "Financial District": 17,
        "Mission District": 10
    },
    "Financial District": {
        "Pacific Heights": 13,
        "Golden Gate Park": 23,
        "The Castro": 20,
        "Bayview": 19,
        "Marina District": 15,
        "Union Square": 9,
        "Sunset District": 30,
        "Alamo Square": 17,
        "Mission District": 17
    },
    "Mission District": {
        "Pacific Heights": 16,
        "Golden Gate Park": 17,
        "The Castro": 7,
        "Bayview": 14,
        "Marina District": 19,
        "Union Square": 15,
        "Sunset District": 24,
        "Alamo Square": 11,
        "Financial District": 15
    }
}

# Ensure all needed travel entries exist
def ttime(a, b):
    if a == b:
        return 0
    if a in travel and b in travel[a]:
        return travel[a][b]
    raise ValueError(f"Missing travel time from {a} to {b}")

n = len(people_data)
names = [p["name"] for p in people_data]
locs = [p["location"] for p in people_data]

opt = Optimize()

start_vars = {p["name"]: Int(f"start_{p['name']}") for p in people_data}
end_vars   = {p["name"]: Int(f"end_{p['name']}")   for p in people_data}
attend_vars= {p["name"]: Bool(f"attend_{p['name']}") for p in people_data}

# Constraints: windows and durations (fix to minimum to make schedule sharp)
for p in people_data:
    name = p["name"]
    win_s = p["win_start"]
    win_e = p["win_end"]
    mdur = p["min_dur"]
    s = start_vars[name]
    e = end_vars[name]
    a = attend_vars[name]

    opt.add(s >= win_s)
    opt.add(e <= win_e)
    # If attending, enforce exact minimum duration, else no duration
    opt.add(e - s == If(a, mdur, 0))
    # Start not after end
    opt.add(e >= s)

# Non-overlap and travel ordering between any two attended meetings
for i in range(n):
    for j in range(i+1, n):
        ni, nj = names[i], names[j]
        li, lj = locs[i], locs[j]
        si, sj = start_vars[ni], start_vars[nj]
        ei, ej = end_vars[ni], end_vars[nj]
        ai, aj = attend_vars[ni], attend_vars[nj]
        tij = ttime(li, lj)
        tji = ttime(lj, li)
        # If both attended, one must precede the other with travel time
        opt.add(Or(Not(And(ai, aj)),
                   ei + tij <= sj,
                   ej + tji <= si))

# Connectivity from start location at 09:00:
# For each attended meeting i, either reachable directly from start, or from some other attended meeting finishing before with travel.
big_M = 24*60  # not strictly used, but kept for reference
for i in range(n):
    ni = names[i]
    li = locs[i]
    si, ei, ai = start_vars[ni], end_vars[ni], attend_vars[ni]
    from_start = si >= start_time + ttime(start_location, li)
    from_others = []
    for j in range(n):
        if j == i:
            continue
        nj = names[j]
        lj = locs[j]
        sj, ej, aj = start_vars[nj], end_vars[nj], attend_vars[nj]
        from_others.append(And(aj, ej + ttime(lj, li) <= si))
    opt.add(Or(Not(ai), from_start, Or(*from_others) if from_others else False))

# Objective 1: maximize number of friends met
total_attended = Sum([If(attend_vars[name], 1, 0) for name in names])
opt.maximize(total_attended)

# Objective 2: prefer meeting Steven if possible (breaks ties toward the plan including Steven)
opt.maximize(If(attend_vars["Steven"], 1, 0))

# Optional Objective 3: maximize total meeting time (they are fixed to minimums here; kept for tie-breaking)
total_meeting_time = Sum([end_vars[name] - start_vars[name] for name in names])
opt.maximize(total_meeting_time)

# Solve
if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
else:
    model = opt.model()
    meetings = []
    for p in people_data:
        name = p["name"]
        if model.eval(attend_vars[name], model_completion=True):
            st = model.eval(start_vars[name]).as_long()
            en = model.eval(end_vars[name]).as_long()
            meetings.append({
                "action": "meet",
                "person": name,
                "start_time": to_hhmm(st),
                "end_time": to_hhmm(en),
                "location": p["location"]
            })
    # Sort by start time
    meetings.sort(key=lambda x: to_minutes(x["start_time"]))
    # Output only requested fields
    out = {"itinerary": [{"action": m["action"], "person": m["person"], "start_time": m["start_time"], "end_time": m["end_time"]} for m in meetings]}
    print(json.dumps(out))