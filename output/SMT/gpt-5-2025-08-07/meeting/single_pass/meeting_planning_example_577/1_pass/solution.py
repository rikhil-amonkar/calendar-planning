# Solve the SF friends scheduling problem with Z3 and print a JSON itinerary.
# Objective: maximize number of friends met subject to windows, minimum durations, and travel times.

from z3 import Int, Bool, If, And, Or, Not, Implies, Optimize
import json

# Minutes helper
def hm_to_min(h, m): return h*60 + m
def min_to_hhmm(m): return f"{m//60:02d}:{m%60:02d}"

# Data
HAIGHT = "Haight-Ashbury"
travel = {
    "Haight-Ashbury": {
        "Russian Hill": 17,
        "Fisherman's Wharf": 23,
        "Nob Hill": 15,
        "Golden Gate Park": 7,
        "Alamo Square": 5,
        "Pacific Heights": 12
    },
    "Russian Hill": {
        "Haight-Ashbury": 17,
        "Fisherman's Wharf": 7,
        "Nob Hill": 5,
        "Golden Gate Park": 21,
        "Alamo Square": 15,
        "Pacific Heights": 7
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22,
        "Russian Hill": 7,
        "Nob Hill": 11,
        "Golden Gate Park": 25,
        "Alamo Square": 20,
        "Pacific Heights": 12
    },
    "Nob Hill": {
        "Haight-Ashbury": 13,
        "Russian Hill": 5,
        "Fisherman's Wharf": 11,
        "Golden Gate Park": 17,
        "Alamo Square": 11,
        "Pacific Heights": 8
    },
    "Golden Gate Park": {
        "Haight-Ashbury": 7,
        "Russian Hill": 19,
        "Fisherman's Wharf": 24,
        "Nob Hill": 20,
        "Alamo Square": 10,
        "Pacific Heights": 16
    },
    "Alamo Square": {
        "Haight-Ashbury": 5,
        "Russian Hill": 13,
        "Fisherman's Wharf": 19,
        "Nob Hill": 11,
        "Golden Gate Park": 9,
        "Pacific Heights": 10
    },
    "Pacific Heights": {
        "Haight-Ashbury": 11,
        "Russian Hill": 7,
        "Fisherman's Wharf": 13,
        "Nob Hill": 8,
        "Golden Gate Park": 15,
        "Alamo Square": 10
    }
}

people = [
    dict(name="Stephanie", location="Russian Hill",       start=hm_to_min(20,0),  end=hm_to_min(20,45), min_dur=15),
    dict(name="Kevin",     location="Fisherman's Wharf",  start=hm_to_min(19,15), end=hm_to_min(21,45), min_dur=75),
    dict(name="Robert",    location="Nob Hill",           start=hm_to_min(7,45),  end=hm_to_min(10,30), min_dur=90),
    dict(name="Steven",    location="Golden Gate Park",   start=hm_to_min(8,30),  end=hm_to_min(17,0),  min_dur=75),
    dict(name="Anthony",   location="Alamo Square",       start=hm_to_min(7,45),  end=hm_to_min(19,45), min_dur=15),
    dict(name="Sandra",    location="Pacific Heights",    start=hm_to_min(14,45), end=hm_to_min(21,45), min_dur=45),
]

arrive_time = hm_to_min(9,0)

# Z3 model
opt = Optimize()

# Variables per person
s_vars = {}
e_vars = {}
meet_vars = {}
for p in people:
    s = Int(f"s_{p['name']}")
    e = Int(f"e_{p['name']}")
    m = Bool(f"meet_{p['name']}")
    s_vars[p['name']] = s
    e_vars[p['name']] = e
    meet_vars[p['name']] = m

    # Bounds
    opt.add(s >= 0, s <= 24*60)
    opt.add(e >= 0, e <= 24*60)

    # Meeting window and duration constraints (minimum duration)
    opt.add(Implies(m, And(
        s >= p['start'],
        e <= p['end'],
        e - s >= p['min_dur']
    )))

    # Must be reachable from starting point at Haight-Ashbury at/after 09:00
    opt.add(Implies(m, s >= arrive_time + travel[HAIGHT][p['location']]))


# Non-overlap with travel: For any pair, if both are met, one precedes the other with travel time
before_bools = {}
for i in range(len(people)):
    for j in range(i+1, len(people)):
        pi = people[i]
        pj = people[j]
        bi = Bool(f"before_{pi['name']}_then_{pj['name']}")
        before_bools[(pi['name'], pj['name'])] = bi
        s_i, e_i = s_vars[pi['name']], e_vars[pi['name']]
        s_j, e_j = s_vars[pj['name']], e_vars[pj['name']]
        m_i, m_j = meet_vars[pi['name']], meet_vars[pj['name']]
        tij = travel[pi['location']][pj['location']]
        tji = travel[pj['location']][pi['location']]

        # If both met and i before j, ensure enough travel time from i to j
        opt.add(Implies(And(m_i, m_j, bi), e_i + tij <= s_j))
        # If both met and j before i, ensure enough travel time from j to i
        opt.add(Implies(And(m_i, m_j, Not(bi)), e_j + tji <= s_i))

# Objective: maximize number of friends met
total_met = sum([If(meet_vars[p['name']], 1, 0) for p in people])
opt.maximize(total_met)

# (Optional) Secondary objective: minimize latest end time among meetings to avoid unnecessary lateness
latest_end = Int("latest_end")
opt.add(latest_end >= 0, latest_end <= 24*60)
# latest_end equals the max e among met meetings (approximate using constraints)
for p in people:
    opt.add(Implies(meet_vars[p['name']], latest_end >= e_vars[p['name']]))
# If nobody is met, latest_end can be 0; otherwise, we'll minimize it.
opt.minimize(latest_end)

# Solve
if opt.check() !=  sat:
    # Shouldn't happen; but print empty itinerary if unsat
    print(json.dumps({"itinerary": []}))
else:
    model = opt.model()

    # Build itinerary from model
    meetings = []
    for p in people:
        if model.evaluate(meet_vars[p['name']], model_completion=True):
            s = model.evaluate(s_vars[p['name']]).as_long()
            e = model.evaluate(e_vars[p['name']]).as_long()
            meetings.append({
                "action": "meet",
                "person": p['name'],
                "start_time": min_to_hhmm(s),
                "end_time": min_to_hhmm(e)
            })

    # Sort by start time
    meetings.sort(key=lambda x: x["start_time"])

    print(json.dumps({"itinerary": meetings}))