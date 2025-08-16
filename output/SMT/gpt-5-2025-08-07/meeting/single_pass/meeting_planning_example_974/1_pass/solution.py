# Solve the San Francisco day scheduling problem with Z3
# Objective: maximize the number of friends met subject to travel times and availability windows

from z3 import *
import json

# Helper to convert HH:MM (24h) to minutes from midnight
def hm_to_min(h, m):
    return h * 60 + m

def str_to_min(s):
    h, m = map(int, s.split(":"))
    return hm_to_min(h, m)

def min_to_hm_str(t):
    h = (t // 60) % 24
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Locations
SUNSET = "Sunset District"
PRESIDIO = "Presidio"
NOB = "Nob Hill"
PACIFIC = "Pacific Heights"
MISSION = "Mission District"
MARINA = "Marina District"
NORTH = "North Beach"
RUSSIAN = "Russian Hill"
RICHMOND = "Richmond District"
EMB = "Embarcadero"
ALAMO = "Alamo Square"

# Directed travel times (minutes)
t = {
    SUNSET: {PRESIDIO:16, NOB:27, PACIFIC:21, MISSION:25, MARINA:21, NORTH:28, RUSSIAN:24, RICHMOND:12, EMB:30, ALAMO:17},
    PRESIDIO: {SUNSET:15, NOB:18, PACIFIC:11, MISSION:26, MARINA:11, NORTH:18, RUSSIAN:14, RICHMOND:7, EMB:20, ALAMO:19},
    NOB: {SUNSET:24, PRESIDIO:17, PACIFIC:8, MISSION:13, MARINA:11, NORTH:8, RUSSIAN:5, RICHMOND:14, EMB:9, ALAMO:11},
    PACIFIC: {SUNSET:21, PRESIDIO:11, NOB:8, MISSION:15, MARINA:6, NORTH:9, RUSSIAN:7, RICHMOND:12, EMB:10, ALAMO:10},
    MISSION: {SUNSET:24, PRESIDIO:25, NOB:12, PACIFIC:16, MARINA:19, NORTH:17, RUSSIAN:15, RICHMOND:20, EMB:19, ALAMO:11},
    MARINA: {SUNSET:19, PRESIDIO:10, NOB:12, PACIFIC:7, MISSION:20, NORTH:11, RUSSIAN:8, RICHMOND:11, EMB:14, ALAMO:15},
    NORTH: {SUNSET:27, PRESIDIO:17, NOB:7, PACIFIC:8, MISSION:18, MARINA:9, RUSSIAN:4, RICHMOND:18, EMB:6, ALAMO:16},
    RUSSIAN: {SUNSET:23, PRESIDIO:14, NOB:5, PACIFIC:7, MISSION:16, MARINA:7, NORTH:5, RICHMOND:14, EMB:8, ALAMO:15},
    RICHMOND: {SUNSET:11, PRESIDIO:7, NOB:17, PACIFIC:10, MISSION:20, MARINA:9, NORTH:17, RUSSIAN:13, EMB:19, ALAMO:13},
    EMB: {SUNSET:30, PRESIDIO:20, NOB:10, PACIFIC:11, MISSION:20, MARINA:12, NORTH:5, RUSSIAN:8, RICHMOND:21, ALAMO:19},
    ALAMO: {SUNSET:16, PRESIDIO:17, NOB:11, PACIFIC:10, MISSION:10, MARINA:15, NORTH:15, RUSSIAN:13, RICHMOND:11, EMB:16},
}

# People with constraints
people = [
    # name, location, availability start, availability end, min duration (min)
    ("Charles", PRESIDIO,  str_to_min("13:15"), str_to_min("15:00"), 105),
    ("Robert", NOB,        str_to_min("13:15"), str_to_min("17:30"),  90),
    ("Nancy", PACIFIC,     str_to_min("14:45"), str_to_min("22:00"), 105),
    ("Brian", MISSION,     str_to_min("15:30"), str_to_min("22:00"),  60),
    ("Kimberly", MARINA,   str_to_min("17:00"), str_to_min("19:45"),  75),
    ("David", NORTH,       str_to_min("14:45"), str_to_min("16:30"),  75),
    ("William", RUSSIAN,   str_to_min("12:30"), str_to_min("19:15"), 120),
    ("Jeffrey", RICHMOND,  str_to_min("12:00"), str_to_min("19:15"),  45),
    ("Karen", EMB,         str_to_min("14:15"), str_to_min("20:45"),  60),
    ("Joshua", ALAMO,      str_to_min("18:45"), str_to_min("22:00"),  60),
]

start_location = SUNSET
arrival_time = str_to_min("09:00")

# Build Z3 model
opt = Optimize()
opt.set("priority", "lex")

# Variables
sel = {}
start = {}
end = {}
loc = {}
dur = {}
avail = {}

for (name, where, a, b, d) in people:
    sel[name] = Bool(f"sel_{name}")
    start[name] = Int(f"start_{name}")
    end[name] = Int(f"end_{name}")
    loc[name] = where
    dur[name] = d
    avail[name] = (a, b)
    # Meeting must lie within availability if selected; durations are fixed to minimum to maximize counts
    opt.add(start[name] >= a)
    opt.add(start[name] <= b - d)
    opt.add(end[name] == start[name] + d)

# No-overlap with travel times between any two selected meetings
names = [p[0] for p in people]
for i in range(len(names)):
    for j in range(i+1, len(names)):
        ni, nj = names[i], names[j]
        tij = t[loc[ni]][loc[nj]]
        tji = t[loc[nj]][loc[ni]]
        opt.add(Implies(And(sel[ni], sel[nj]),
                        Or(end[ni] + tij <= start[nj],
                           end[nj] + tji <= start[ni])))

# Ensure the first selected meeting is reachable from the start (this is redundant here but keeps model general)
for name in names:
    reachable_from_start = (start[name] >= arrival_time + t[start_location][loc[name]])
    reachable_from_other = False
    ors = []
    for other in names:
        if other == name:
            continue
        ors.append(And(sel[other], end[other] + t[loc[other]][loc[name]] <= start[name]))
    if ors:
        reachable_from_other = Or(*ors)
        opt.add(Implies(sel[name], Or(reachable_from_start, reachable_from_other)))
    else:
        opt.add(Implies(sel[name], reachable_from_start))

# Objectives: maximize number of meetings, then minimize total meeting time (tie-breaker),
# then minimize sum of start times (prefer earlier schedules)
num_meetings = Sum([If(sel[n], 1, 0) for n in names])
total_meeting_time = Sum([If(sel[n], dur[n], 0) for n in names])
sum_start_times = Sum([If(sel[n], start[n], 0) for n in names])

opt.maximize(num_meetings)
opt.minimize(total_meeting_time)
opt.minimize(sum_start_times)

if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()
    chosen = []
    for name in names:
        if m.eval(sel[name], model_completion=True):
            s = m.eval(start[name], model_completion=True).as_long()
            e = m.eval(end[name], model_completion=True).as_long()
            chosen.append((s, e, name))
    chosen.sort(key=lambda x: x[0])
    itinerary = []
    for s, e, name in chosen:
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": min_to_hm_str(s),
            "end_time": min_to_hm_str(e),
        })
    print(json.dumps({"itinerary": itinerary}))