'SOLUTION:'

from z3 import *
import json

# Time helpers
def to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Locations
locations = [
    "Chinatown", "Embarcadero", "Pacific Heights", "Russian Hill",
    "Haight-Ashbury", "Golden Gate Park", "Fisherman's Wharf",
    "Sunset District", "The Castro"
]

# Travel times (minutes)
tt = {
    "Chinatown": {
        "Embarcadero": 5,
        "Pacific Heights": 10,
        "Russian Hill": 7,
        "Haight-Ashbury": 19,
        "Golden Gate Park": 23,
        "Fisherman's Wharf": 8,
        "Sunset District": 29,
        "The Castro": 22
    },
    "Embarcadero": {
        "Chinatown": 7,
        "Pacific Heights": 11,
        "Russian Hill": 8,
        "Haight-Ashbury": 21,
        "Golden Gate Park": 25,
        "Fisherman's Wharf": 6,
        "Sunset District": 30,
        "The Castro": 25
    },
    "Pacific Heights": {
        "Chinatown": 11,
        "Embarcadero": 10,
        "Russian Hill": 7,
        "Haight-Ashbury": 11,
        "Golden Gate Park": 15,
        "Fisherman's Wharf": 13,
        "Sunset District": 21,
        "The Castro": 16
    },
    "Russian Hill": {
        "Chinatown": 9,
        "Embarcadero": 8,
        "Pacific Heights": 7,
        "Haight-Ashbury": 17,
        "Golden Gate Park": 21,
        "Fisherman's Wharf": 7,
        "Sunset District": 23,
        "The Castro": 21
    },
    "Haight-Ashbury": {
        "Chinatown": 19,
        "Embarcadero": 20,
        "Pacific Heights": 12,
        "Russian Hill": 17,
        "Golden Gate Park": 7,
        "Fisherman's Wharf": 23,
        "Sunset District": 15,
        "The Castro": 6
    },
    "Golden Gate Park": {
        "Chinatown": 23,
        "Embarcadero": 25,
        "Pacific Heights": 16,
        "Russian Hill": 19,
        "Haight-Ashbury": 7,
        "Fisherman's Wharf": 24,
        "Sunset District": 10,
        "The Castro": 13
    },
    "Fisherman's Wharf": {
        "Chinatown": 12,
        "Embarcadero": 8,
        "Pacific Heights": 12,
        "Russian Hill": 7,
        "Haight-Ashbury": 22,
        "Golden Gate Park": 25,
        "Sunset District": 27,
        "The Castro": 27
    },
    "Sunset District": {
        "Chinatown": 30,
        "Embarcadero": 30,
        "Pacific Heights": 21,
        "Russian Hill": 24,
        "Haight-Ashbury": 15,
        "Golden Gate Park": 11,
        "Fisherman's Wharf": 29,
        "The Castro": 17
    },
    "The Castro": {
        "Chinatown": 22,
        "Embarcadero": 22,
        "Pacific Heights": 16,
        "Russian Hill": 18,
        "Haight-Ashbury": 6,
        "Golden Gate Park": 11,
        "Fisherman's Wharf": 24,
        "Sunset District": 17
    }
}

def travel_time(a, b):
    if a == b:
        return 0
    return tt[a][b]

# Friends availability and required minimum meeting durations
friends = {
    "Richard":  {"location": "Embarcadero",       "start": to_minutes("15:15"), "end": to_minutes("18:45"), "min": 90},
    "Mark":     {"location": "Pacific Heights",   "start": to_minutes("15:00"), "end": to_minutes("17:00"), "min": 45},
    "Matthew":  {"location": "Russian Hill",      "start": to_minutes("17:30"), "end": to_minutes("21:00"), "min": 90},
    "Rebecca":  {"location": "Haight-Ashbury",    "start": to_minutes("14:45"), "end": to_minutes("18:00"), "min": 60},
    "Melissa":  {"location": "Golden Gate Park",  "start": to_minutes("13:45"), "end": to_minutes("17:30"), "min": 90},
    "Margaret": {"location": "Fisherman's Wharf", "start": to_minutes("14:45"), "end": to_minutes("20:15"), "min": 15},
    "Emily":    {"location": "Sunset District",   "start": to_minutes("15:45"), "end": to_minutes("17:00"), "min": 45},
    "George":   {"location": "The Castro",        "start": to_minutes("14:00"), "end": to_minutes("16:15"), "min": 75},
}

# Start at Chinatown at 9:00
start_location = "Chinatown"
arrival_time_at_start = to_minutes("9:00")  # 540

# Build Z3 model
opt = Optimize()
opt.set(priority='lex')

# Variables
Start = {}
End = {}
Meet = {}

for p in friends:
    Start[p] = Int(f"start_{p}")
    End[p] = Int(f"end_{p}")
    Meet[p] = Bool(f"meet_{p}")

    # Domain constraints
    opt.add(Start[p] >= 0)
    opt.add(End[p] >= 0)
    opt.add(End[p] >= Start[p])

    # If meeting, enforce availability, duration, and feasible arrival from start
    loc = friends[p]["location"]
    window_start = friends[p]["start"]
    window_end = friends[p]["end"]
    min_dur = friends[p]["min"]

    # Meeting implies constraints
    opt.add(Implies(Meet[p], And(
        Start[p] >= window_start,
        End[p] <= window_end,
        End[p] - Start[p] >= min_dur,
        Start[p] >= arrival_time_at_start + travel_time(start_location, loc)
    )))
    # If not meeting, collapse interval
    opt.add(Implies(Not(Meet[p]), And(Start[p] == 0, End[p] == 0)))

# Pairwise non-overlap with travel times
people = list(friends.keys())
for i in range(len(people)):
    for j in range(i + 1, len(people)):
        a = people[i]
        b = people[j]
        la = friends[a]["location"]
        lb = friends[b]["location"]
        ta_to_b = travel_time(la, lb)
        tb_to_a = travel_time(lb, la)
        opt.add(Or(
            Not(Meet[a]),
            Not(Meet[b]),
            End[a] + ta_to_b <= Start[b],
            End[b] + tb_to_a <= Start[a]
        ))

# Objectives: maximize number of meetings, then total meeting minutes
total_meetings = Sum([If(Meet[p], 1, 0) for p in people])
total_minutes = Sum([If(Meet[p], End[p] - Start[p], 0) for p in people])
opt.maximize(total_meetings)
opt.maximize(total_minutes)

# Solve
if opt.check() != sat:
    # If somehow unsat, output empty itinerary
    result = {"itinerary": []}
    print(json.dumps(result, ensure_ascii=False))
else    :
    model = opt.model()
    selected = []
    for p in people:
        if is_true(model.eval(Meet[p], model_completion=True)):
            s = model.eval(Start[p], model_completion=True).as_long()
            e = model.eval(End[p], model_completion=True).as_long()
            selected.append((s, e, p, friends[p]["location"]))
    # Sort by start time
    selected.sort(key=lambda x: x[0])

    itinerary = []
    for s, e, p, loc in selected:
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": p,
            "start_time": minutes_to_str(s),
            "end_time": minutes_to_str(e)
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))