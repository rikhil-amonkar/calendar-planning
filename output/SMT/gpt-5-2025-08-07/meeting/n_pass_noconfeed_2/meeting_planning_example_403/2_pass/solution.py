# SOLUTION (fixed check() result handling and boolean evaluation):
import json
from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, Implies, sat, is_true

def minutes(h, m):
    return h * 60 + m

def parse_time(t):
    # t like '11:45' or '9:00'
    h, m = t.split(':')
    return minutes(int(h), int(m))

def fmt_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

# Input data
locations = [
    "Union Square",
    "Golden Gate Park",
    "Pacific Heights",
    "Presidio",
    "Chinatown",
    "The Castro"
]

# Travel times (directional, in minutes)
travel_times = {
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "The Castro"): 19,

    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "The Castro"): 13,

    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "The Castro"): 16,

    ("Presidio", "Union Square"): 22,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "The Castro"): 21,

    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "The Castro"): 22,

    ("The Castro", "Union Square"): 19,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Chinatown"): 20,
}

def travel(a, b):
    if a == b:
        return 0
    return travel_times[(a, b)]

start_location = "Union Square"
start_time_str = "9:00"
start_time = parse_time(start_time_str)

people = {
    "Andrew": {
        "location": "Golden Gate Park",
        "window": ("11:45", "14:30"),
        "min_duration": 75
    },
    "Sarah": {
        "location": "Pacific Heights",
        "window": ("16:15", "18:45"),
        "min_duration": 15
    },
    "Nancy": {
        "location": "Presidio",
        "window": ("17:30", "19:15"),
        "min_duration": 60
    },
    "Rebecca": {
        "location": "Chinatown",
        "window": ("9:45", "21:30"),
        "min_duration": 90
    },
    "Robert": {
        "location": "The Castro",
        "window": ("8:30", "14:15"),
        "min_duration": 30
    }
}

# Convert windows to minutes
for p, info in people.items():
    s_str, e_str = info["window"]
    info["win_start"] = parse_time(s_str)
    info["win_end"] = parse_time(e_str)

# Build SMT model
opt = Optimize()
opt.set(priority='lex')

start_vars = {}
dur_vars = {}
meet_vars = {}

DAY_END = 24 * 60

for p, info in people.items():
    start_vars[p] = Int(f"{p}_start")
    dur_vars[p] = Int(f"{p}_dur")
    meet_vars[p] = Bool(f"{p}_meet")

    s = start_vars[p]
    d = dur_vars[p]
    m = meet_vars[p]
    win_s = info["win_start"]
    win_e = info["win_end"]
    min_d = info["min_duration"]

    # General bounds
    opt.add(s >= 0, s <= DAY_END)
    opt.add(d >= 0)

    # If meeting person p
    opt.add(Implies(m, And(
        s >= win_s,
        s + d <= win_e,
        d >= min_d,
        # Must be reachable from start
        s >= start_time + travel(start_location, info["location"])
    )))

    # If not meeting, duration is zero
    opt.add(Implies(Not(m), d == 0))

# Pairwise non-overlap and travel-time constraints
people_list = list(people.keys())
for i in range(len(people_list)):
    for j in range(i + 1, len(people_list)):
        pi = people_list[i]
        pj = people_list[j]
        mi = meet_vars[pi]
        mj = meet_vars[pj]
        si = start_vars[pi]
        sj = start_vars[pj]
        di = dur_vars[pi]
        dj = dur_vars[pj]
        li = people[pi]["location"]
        lj = people[pj]["location"]

        opt.add(Implies(And(mi, mj), Or(
            sj >= si + di + travel(li, lj),
            si >= sj + dj + travel(lj, li)
        )))

# Objectives
meet_count = Sum([If(meet_vars[p], 1, 0) for p in people_list])
total_meeting_minutes = Sum([dur_vars[p] for p in people_list])

opt.maximize(meet_count)
opt.maximize(total_meeting_minutes)

res = opt.check()
if res != sat:
    # No feasible solution
    result = {"itinerary": []}
    print(json.dumps(result))
else:
    model = opt.model()
    itinerary = []
    for p in people_list:
        if is_true(model.eval(meet_vars[p], model_completion=True)):
            s = model.eval(start_vars[p], model_completion=True).as_long()
            d = model.eval(dur_vars[p], model_completion=True).as_long()
            e = s + d
            itinerary.append({
                "action": "meet",
                "location": people[p]["location"],
                "person": p,
                "start_time": fmt_time(s),
                "end_time": fmt_time(e)
            })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: parse_time(x["start_time"]))
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))