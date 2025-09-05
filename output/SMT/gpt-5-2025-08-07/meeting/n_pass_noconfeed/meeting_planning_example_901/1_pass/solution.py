import json
from z3 import *

def minutes(h, m):
    return h*60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Locations
L = [
    "Russian Hill",
    "Pacific Heights",
    "North Beach",
    "Golden Gate Park",
    "Embarcadero",
    "Haight-Ashbury",
    "Fisherman's Wharf",
    "Mission District",
    "Alamo Square",
    "Bayview",
    "Richmond District",
]

# Travel times (minutes)
T = {
    "Russian Hill": {
        "Pacific Heights": 7,
        "North Beach": 5,
        "Golden Gate Park": 21,
        "Embarcadero": 8,
        "Haight-Ashbury": 17,
        "Fisherman's Wharf": 7,
        "Mission District": 16,
        "Alamo Square": 15,
        "Bayview": 23,
        "Richmond District": 14,
    },
    "Pacific Heights": {
        "Russian Hill": 7,
        "North Beach": 9,
        "Golden Gate Park": 15,
        "Embarcadero": 10,
        "Haight-Ashbury": 11,
        "Fisherman's Wharf": 13,
        "Mission District": 15,
        "Alamo Square": 10,
        "Bayview": 22,
        "Richmond District": 12,
    },
    "North Beach": {
        "Russian Hill": 4,
        "Pacific Heights": 8,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Haight-Ashbury": 18,
        "Fisherman's Wharf": 5,
        "Mission District": 18,
        "Alamo Square": 16,
        "Bayview": 25,
        "Richmond District": 18,
    },
    "Golden Gate Park": {
        "Russian Hill": 19,
        "Pacific Heights": 16,
        "North Beach": 23,
        "Embarcadero": 25,
        "Haight-Ashbury": 7,
        "Fisherman's Wharf": 24,
        "Mission District": 17,
        "Alamo Square": 9,
        "Bayview": 23,
        "Richmond District": 7,
    },
    "Embarcadero": {
        "Russian Hill": 8,
        "Pacific Heights": 11,
        "North Beach": 5,
        "Golden Gate Park": 25,
        "Haight-Ashbury": 21,
        "Fisherman's Wharf": 6,
        "Mission District": 20,
        "Alamo Square": 19,
        "Bayview": 21,
        "Richmond District": 21,
    },
    "Haight-Ashbury": {
        "Russian Hill": 17,
        "Pacific Heights": 12,
        "North Beach": 19,
        "Golden Gate Park": 7,
        "Embarcadero": 20,
        "Fisherman's Wharf": 23,
        "Mission District": 11,
        "Alamo Square": 5,
        "Bayview": 18,
        "Richmond District": 10,
    },
    "Fisherman's Wharf": {
        "Russian Hill": 7,
        "Pacific Heights": 12,
        "North Beach": 6,
        "Golden Gate Park": 25,
        "Embarcadero": 8,
        "Haight-Ashbury": 22,
        "Mission District": 22,
        "Alamo Square": 21,
        "Bayview": 26,
        "Richmond District": 18,
    },
    "Mission District": {
        "Russian Hill": 15,
        "Pacific Heights": 16,
        "North Beach": 17,
        "Golden Gate Park": 17,
        "Embarcadero": 19,
        "Haight-Ashbury": 12,
        "Fisherman's Wharf": 22,
        "Alamo Square": 11,
        "Bayview": 14,
        "Richmond District": 20,
    },
    "Alamo Square": {
        "Russian Hill": 13,
        "Pacific Heights": 10,
        "North Beach": 15,
        "Golden Gate Park": 9,
        "Embarcadero": 16,
        "Haight-Ashbury": 5,
        "Fisherman's Wharf": 19,
        "Mission District": 10,
        "Bayview": 16,
        "Richmond District": 11,
    },
    "Bayview": {
        "Russian Hill": 23,
        "Pacific Heights": 23,
        "North Beach": 22,
        "Golden Gate Park": 22,
        "Embarcadero": 19,
        "Haight-Ashbury": 19,
        "Fisherman's Wharf": 25,
        "Mission District": 13,
        "Alamo Square": 16,
        "Richmond District": 25,
    },
    "Richmond District": {
        "Russian Hill": 13,
        "Pacific Heights": 10,
        "North Beach": 17,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Haight-Ashbury": 10,
        "Fisherman's Wharf": 18,
        "Mission District": 20,
        "Alamo Square": 13,
        "Bayview": 27,
    },
}

# Participants: name, location, availability [start, end], minimum meeting minutes
participants = [
    ("Emily", "Pacific Heights", minutes(9,15), minutes(13,45), 120),
    ("Helen", "North Beach", minutes(13,45), minutes(18,45), 30),
    ("Kimberly", "Golden Gate Park", minutes(18,45), minutes(21,15), 75),
    ("James", "Embarcadero", minutes(10,30), minutes(11,30), 30),
    ("Linda", "Haight-Ashbury", minutes(7,30), minutes(19,15), 15),
    ("Paul", "Fisherman's Wharf", minutes(14,45), minutes(18,45), 90),
    ("Anthony", "Mission District", minutes(8,0), minutes(14,45), 105),
    ("Nancy", "Alamo Square", minutes(8,30), minutes(13,45), 120),
    ("William", "Bayview", minutes(17,30), minutes(20,30), 120),
    ("Margaret", "Richmond District", minutes(15,15), minutes(18,15), 45),
]

# Origin and start time
origin_loc = "Russian Hill"
arrival_time = minutes(9,0)

# Build Z3 model
opt = Optimize()

# Variables per participant
starts = {}
ends = {}
meet = {}
for name, loc, a_start, a_end, min_dur in participants:
    starts[name] = Int(f"start_{name}")
    ends[name] = Int(f"end_{name}")
    meet[name] = Int(f"meet_{name}")  # 0 or 1
    opt.add(meet[name] >= 0, meet[name] <= 1)
    # Time bounds for safety
    opt.add(starts[name] >= 0, starts[name] <= minutes(23,59))
    opt.add(ends[name] >= 0, ends[name] <= minutes(23,59))
    # If meeting, must respect availability and minimum duration
    opt.add(Implies(meet[name] == 1, And(
        starts[name] >= a_start,
        ends[name] <= a_end,
        ends[name] > starts[name],
        ends[name] - starts[name] >= min_dur
    )))
    # If meeting, must be reachable from origin at 9:00
    opt.add(Implies(meet[name] == 1, starts[name] >= arrival_time + T[origin_loc][loc]))

# Pairwise disjunctive scheduling with travel times
# For each pair (i, j), if both are met then either i happens before j with travel, or j before i with travel
order_vars = {}
for i in range(len(participants)):
    name_i, loc_i, _, _, _ = participants[i]
    for j in range(i+1, len(participants)):
        name_j, loc_j, _, _, _ = participants[j]
        b = Bool(f"before_{name_i}_then_{name_j}")
        order_vars[(name_i, name_j)] = b
        # Only enforce ordering if both are met
        cond_both = And(meet[name_i] == 1, meet[name_j] == 1)
        opt.add(Implies(cond_both, Or(
            And(b, starts[name_j] >= ends[name_i] + T[loc_i][loc_j]),
            And(Not(b), starts[name_i] >= ends[name_j] + T[loc_j][loc_i])
        )))

# Objective: maximize number of friends met, then maximize total meeting minutes
num_met = Sum([meet[name] for name, _, _, _, _ in participants])
total_minutes = Sum([
    If(meet[name] == 1, ends[name] - starts[name], 0)
    for name, _, _, _, _ in participants
])

opt.maximize(num_met)
opt.maximize(total_minutes)

# Solve
if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
    raise SystemExit()

m = opt.model()

# Build itinerary
events = []
for name, loc, a_start, a_end, min_dur in participants:
    if m.eval(meet[name]).as_long() == 1:
        s = m.eval(starts[name]).as_long()
        e = m.eval(ends[name]).as_long()
        events.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": fmt_time(s),
            "end_time": fmt_time(e)
        })

# Sort by start time
events.sort(key=lambda x: (int(x["start_time"].split(":")[0])*60 + int(x["start_time"].split(":")[1])))

print(json.dumps({"itinerary": events}, ensure_ascii=False))