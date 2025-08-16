# Solve the scheduling problem using Z3 and output an optimal itinerary
# maximizing the number of friends met subject to travel times and windows.

from z3 import Optimize, Int, Bool, If, And, Or, Implies, Sum, is_true
import json

def time_to_minutes(tstr):
    h, m = map(int, tstr.split(":"))
    return 60*h + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

# Data
start_location = "Financial District"
start_time = time_to_minutes("09:00")

friends = [
    {
        "name": "Nancy",
        "location": "Chinatown",
        "window_start": time_to_minutes("09:30"),
        "window_end": time_to_minutes("13:30"),
        "min_duration": 90
    },
    {
        "name": "Mary",
        "location": "Alamo Square",
        "window_start": time_to_minutes("07:00"),
        "window_end": time_to_minutes("21:00"),
        "min_duration": 75
    },
    {
        "name": "Jessica",
        "location": "Bayview",
        "window_start": time_to_minutes("11:15"),
        "window_end": time_to_minutes("13:45"),
        "min_duration": 45
    },
    {
        "name": "Rebecca",
        "location": "Fisherman's Wharf",
        "window_start": time_to_minutes("07:00"),
        "window_end": time_to_minutes("08:30"),
        "min_duration": 45
    },
]

# Directed travel times (minutes)
T = {
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Bayview"): 22,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Chinatown"): 16,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Chinatown"): 18,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Alamo Square"): 20,
    ("Fisherman's Wharf", "Bayview"): 26,
}

def travel(a, b):
    return T[(a, b)]

# Z3 model
opt = Optimize()

names = [f["name"] for f in friends]
loc = {f["name"]: f["location"] for f in friends}
win_start = {f["name"]: f["window_start"] for f in friends}
win_end = {f["name"]: f["window_end"] for f in friends}
dur = {f["name"]: f["min_duration"] for f in friends}

start_vars = {n: Int(f"start_{n}") for n in names}
meet_vars = {n: Bool(f"meet_{n}") for n in names}

# Bounds and window constraints
for n in names:
    s = start_vars[n]
    m = meet_vars[n]
    # Domain of start time
    opt.add(s >= 0, s <= 24*60)
    # If we meet, it must be within window and at least travel time from start location
    opt.add(Implies(m, And(
        s >= win_start[n],
        s + dur[n] <= win_end[n],
        s >= start_time + travel(start_location, loc[n])
    )))

# No-overlap and travel feasibility between meetings
for i in range(len(names)):
    for j in range(i+1, len(names)):
        ni, nj = names[i], names[j]
        mi, mj = meet_vars[ni], meet_vars[nj]
        si, sj = start_vars[ni], start_vars[nj]
        di, dj = dur[ni], dur[nj]
        tij = travel(loc[ni], loc[nj])
        tji = travel(loc[nj], loc[ni])
        # If both meetings happen, enforce order with travel times
        opt.add(Implies(And(mi, mj),
                        Or(si + di + tij <= sj,
                           sj + dj + tji <= si)))

# Objective: maximize number of meetings
meet_ints = [If(meet_vars[n], 1, 0) for n in names]
h1 = opt.maximize(Sum(meet_ints))

# Optional secondary: minimize total finish time to pick an earlier-day plan
# This doesn't change optimality on count; it just breaks ties.
finish_times = [If(meet_vars[n], start_vars[n] + dur[n], 0) for n in names]
opt.minimize(Sum(finish_times))

# Solve
res = opt.check()
if str(res) != "sat":
    print(json.dumps({"itinerary": []}))
else:
    model = opt.model()
    meetings = []
    for n in names:
        if is_true(model.eval(meet_vars[n])):
            s = model.eval(start_vars[n]).as_long()
            e = s + dur[n]
            meetings.append({
                "action": "meet",
                "person": n,
                "start": s,
                "end": e
            })
    # Sort by start time
    meetings.sort(key=lambda x: x["start"])
    # Format times
    itinerary = []
    for m in meetings:
        itinerary.append({
            "action": "meet",
            "person": m["person"],
            "start_time": minutes_to_time(m["start"]),
            "end_time": minutes_to_time(m["end"])
        })
    print(json.dumps({"itinerary": itinerary}))