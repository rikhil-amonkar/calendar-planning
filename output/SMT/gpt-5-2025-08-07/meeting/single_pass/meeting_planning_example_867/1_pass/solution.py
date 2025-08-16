# Requires: z3-solver (pip install z3-solver)

from z3 import *
import json

def t(h, m):
    return h * 60 + m

def fmt(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Locations
HA = "Haight-Ashbury"

travel = {
    "Haight-Ashbury": {
        "Mission District": 11, "Union Square": 19, "Pacific Heights": 12, "Bayview": 18,
        "Fisherman's Wharf": 23, "Marina District": 17, "Richmond District": 10,
        "Sunset District": 15, "Golden Gate Park": 7
    },
    "Mission District": {
        "Haight-Ashbury": 12, "Union Square": 15, "Pacific Heights": 16, "Bayview": 14,
        "Fisherman's Wharf": 22, "Marina District": 19, "Richmond District": 20,
        "Sunset District": 24, "Golden Gate Park": 17
    },
    "Union Square": {
        "Haight-Ashbury": 18, "Mission District": 14, "Pacific Heights": 15, "Bayview": 15,
        "Fisherman's Wharf": 15, "Marina District": 18, "Richmond District": 20,
        "Sunset District": 27, "Golden Gate Park": 22
    },
    "Pacific Heights": {
        "Haight-Ashbury": 11, "Mission District": 15, "Union Square": 12, "Bayview": 22,
        "Fisherman's Wharf": 13, "Marina District": 6, "Richmond District": 12,
        "Sunset District": 21, "Golden Gate Park": 15
    },
    "Bayview": {
        "Haight-Ashbury": 19, "Mission District": 13, "Union Square": 18, "Pacific Heights": 23,
        "Fisherman's Wharf": 25, "Marina District": 27, "Richmond District": 25,
        "Sunset District": 23, "Golden Gate Park": 22
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22, "Mission District": 22, "Union Square": 13, "Pacific Heights": 12,
        "Bayview": 26, "Marina District": 9, "Richmond District": 18,
        "Sunset District": 27, "Golden Gate Park": 25
    },
    "Marina District": {
        "Haight-Ashbury": 16, "Mission District": 20, "Union Square": 16, "Pacific Heights": 7,
        "Bayview": 27, "Fisherman's Wharf": 10, "Richmond District": 11,
        "Sunset District": 19, "Golden Gate Park": 18
    },
    "Richmond District": {
        "Haight-Ashbury": 10, "Mission District": 20, "Union Square": 21, "Pacific Heights": 10,
        "Bayview": 27, "Fisherman's Wharf": 18, "Marina District": 9,
        "Sunset District": 11, "Golden Gate Park": 9
    },
    "Sunset District": {
        "Haight-Ashbury": 15, "Mission District": 25, "Union Square": 30, "Pacific Heights": 21,
        "Bayview": 22, "Fisherman's Wharf": 29, "Marina District": 21,
        "Richmond District": 12, "Golden Gate Park": 11
    },
    "Golden Gate Park": {
        "Haight-Ashbury": 7, "Mission District": 17, "Union Square": 22, "Pacific Heights": 16,
        "Bayview": 23, "Fisherman's Wharf": 24, "Marina District": 16,
        "Richmond District": 7, "Sunset District": 10
    }
}

friends = [
    # name, location, window_start, window_end, min_duration (minutes)
    ("Elizabeth", "Mission District", t(10,30), t(20,0), 90),
    ("David", "Union Square", t(15,15), t(19,0), 45),
    ("Sandra", "Pacific Heights", t(7,0), t(20,0), 120),
    ("Thomas", "Bayview", t(19,30), t(20,30), 30),
    ("Robert", "Fisherman's Wharf", t(10,0), t(15,0), 15),
    ("Kenneth", "Marina District", t(10,45), t(13,0), 45),
    ("Melissa", "Richmond District", t(18,15), t(20,0), 15),
    ("Kimberly", "Sunset District", t(10,15), t(18,15), 105),
    ("Amanda", "Golden Gate Park", t(7,45), t(18,45), 15),
]

start_location = HA
arrival_time = t(9,0)

opt = Optimize()

meet = {}
start = {}
end = {}
M = 24 * 60

for (name, loc, w_start, w_end, dmin) in friends:
    meet[name] = Bool(f"meet_{name}")
    start[name] = Int(f"start_{name}")
    end[name] = Int(f"end_{name}")

    # Time bounds
    opt.add(And(start[name] >= 0, start[name] <= M))
    opt.add(And(end[name] >= 0, end[name] <= M))

    # If meeting, respect window and duration
    opt.add(Implies(meet[name], And(
        start[name] >= w_start,
        end[name] <= w_end,
        end[name] - start[name] >= dmin,
        start[name] < end[name]
    )))
    # If not meeting, allow degenerate start/end
    opt.add(Implies(Not(meet[name]), And(
        start[name] == 0, end[name] == 0
    )))

    # Lower bound due to initial travel from Haight-Ashbury at 09:00
    # This is a safe lower bound even if not the first meeting.
    opt.add(Implies(meet[name], start[name] >= arrival_time + travel[start_location][loc]))

# Disjunctive no-overlap with travel times
for i in range(len(friends)):
    name_i, loc_i, _, _, _ = friends[i]
    for j in range(i+1, len(friends)):
        name_j, loc_j, _, _, _ = friends[j]
        tij = travel[loc_i][loc_j]
        tji = travel[loc_j][loc_i]
        opt.add(Implies(And(meet[name_i], meet[name_j]),
                        Or(end[name_i] + tij <= start[name_j],
                           end[name_j] + tji <= start[name_i])))

# Objectives: maximize number of meetings, then minimize the latest end time
num_met = Sum([If(meet[name], 1, 0) for (name, *_rest) in friends])
last_end = Int("last_end")
opt.add(last_end >= 0)
for (name, *_rest) in friends:
    opt.add(Implies(meet[name], last_end >= end[name]))
opt.maximize(num_met)
opt.minimize(last_end)
# Optional tie-breaker: minimize sum of meeting durations to prefer tighter schedules
total_duration = Sum([If(meet[name], end[name] - start[name], 0) for (name, *_rest) in friends])
opt.minimize(total_duration)

if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
else:
    model = opt.model()
    meetings = []
    for (name, loc, w_start, w_end, dmin) in friends:
        if is_true(model.eval(meet[name])):
            s = model.eval(start[name]).as_long()
            e = model.eval(end[name]).as_long()
            meetings.append({
                "action": "meet",
                "person": name,
                "start_time": fmt(s),
                "end_time": fmt(e),
            })
    meetings.sort(key=lambda x: x["start_time"])
    print(json.dumps({"itinerary": meetings}))