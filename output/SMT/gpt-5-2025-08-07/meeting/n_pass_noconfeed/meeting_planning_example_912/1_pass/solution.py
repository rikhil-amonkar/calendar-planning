import json
from z3 import *

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Travel times (minutes)
travel = {
    "Union Square": {
        "Presidio": 24, "Alamo Square": 15, "Marina District": 18, "Financial District": 9,
        "Nob Hill": 9, "Sunset District": 27, "Chinatown": 7, "Russian Hill": 13,
        "North Beach": 10, "Haight-Ashbury": 18
    },
    "Presidio": {
        "Union Square": 22, "Alamo Square": 19, "Marina District": 11, "Financial District": 23,
        "Nob Hill": 18, "Sunset District": 15, "Chinatown": 21, "Russian Hill": 14,
        "North Beach": 18, "Haight-Ashbury": 15
    },
    "Alamo Square": {
        "Union Square": 14, "Presidio": 17, "Marina District": 15, "Financial District": 17,
        "Nob Hill": 11, "Sunset District": 16, "Chinatown": 15, "Russian Hill": 13,
        "North Beach": 15, "Haight-Ashbury": 5
    },
    "Marina District": {
        "Union Square": 16, "Presidio": 10, "Alamo Square": 15, "Financial District": 17,
        "Nob Hill": 12, "Sunset District": 19, "Chinatown": 15, "Russian Hill": 8,
        "North Beach": 11, "Haight-Ashbury": 16
    },
    "Financial District": {
        "Union Square": 9, "Presidio": 22, "Alamo Square": 17, "Marina District": 15,
        "Nob Hill": 8, "Sunset District": 30, "Chinatown": 5, "Russian Hill": 11,
        "North Beach": 7, "Haight-Ashbury": 19
    },
    "Nob Hill": {
        "Union Square": 7, "Presidio": 17, "Alamo Square": 11, "Marina District": 11,
        "Financial District": 9, "Sunset District": 24, "Chinatown": 6, "Russian Hill": 5,
        "North Beach": 8, "Haight-Ashbury": 13
    },
    "Sunset District": {
        "Union Square": 30, "Presidio": 16, "Alamo Square": 17, "Marina District": 21,
        "Financial District": 30, "Nob Hill": 27, "Chinatown": 30, "Russian Hill": 24,
        "North Beach": 28, "Haight-Ashbury": 15
    },
    "Chinatown": {
        "Union Square": 7, "Presidio": 19, "Alamo Square": 17, "Marina District": 12,
        "Financial District": 5, "Nob Hill": 9, "Sunset District": 29, "Russian Hill": 7,
        "North Beach": 3, "Haight-Ashbury": 19
    },
    "Russian Hill": {
        "Union Square": 10, "Presidio": 14, "Alamo Square": 15, "Marina District": 7,
        "Financial District": 11, "Nob Hill": 5, "Sunset District": 23, "Chinatown": 9,
        "North Beach": 5, "Haight-Ashbury": 17
    },
    "North Beach": {
        "Union Square": 7, "Presidio": 17, "Alamo Square": 16, "Marina District": 9,
        "Financial District": 8, "Nob Hill": 7, "Sunset District": 27, "Chinatown": 6,
        "Russian Hill": 4, "Haight-Ashbury": 18
    },
    "Haight-Ashbury": {
        "Union Square": 19, "Presidio": 15, "Alamo Square": 5, "Marina District": 17,
        "Financial District": 21, "Nob Hill": 15, "Sunset District": 15, "Chinatown": 19,
        "Russian Hill": 17, "North Beach": 19
    }
}

# People and their constraints
people = [
    {"name": "Kimberly", "location": "Presidio", "start": 15*60+30, "end": 16*60+0, "min": 15},
    {"name": "Elizabeth", "location": "Alamo Square", "start": 19*60+15, "end": 20*60+15, "min": 15},
    {"name": "Joshua", "location": "Marina District", "start": 10*60+30, "end": 14*60+15, "min": 45},
    {"name": "Sandra", "location": "Financial District", "start": 19*60+30, "end": 20*60+15, "min": 45},
    {"name": "Kenneth", "location": "Nob Hill", "start": 12*60+45, "end": 21*60+45, "min": 30},
    {"name": "Betty", "location": "Sunset District", "start": 14*60+0, "end": 19*60+0, "min": 60},
    {"name": "Deborah", "location": "Chinatown", "start": 17*60+15, "end": 20*60+30, "min": 15},
    {"name": "Barbara", "location": "Russian Hill", "start": 17*60+30, "end": 21*60+15, "min": 120},
    {"name": "Steven", "location": "North Beach", "start": 17*60+45, "end": 20*60+45, "min": 90},
    {"name": "Daniel", "location": "Haight-Ashbury", "start": 18*60+30, "end": 18*60+45, "min": 15}
]

start_location = "Union Square"
arrival_time = 9*60  # 9:00

# Build solver
opt = Optimize()

meet_vars = {}
start_vars = {}
end_vars = {}

# Variables and constraints per person
for p in people:
    name = p["name"]
    meet = Bool(f"meet_{name}")
    s = Int(f"start_{name}")
    e = Int(f"end_{name}")
    meet_vars[name] = meet
    start_vars[name] = s
    end_vars[name] = e

    # Base domains
    opt.add(s >= 0, e >= 0)

    # Meeting constraints if chosen
    opt.add(Implies(meet, And(
        s >= p["start"],
        e <= p["end"],
        e - s >= p["min"],
        s >= arrival_time + travel[start_location][p["location"]]
    )))
    # If not meeting, set to 0 length to simplify model
    opt.add(Implies(Not(meet), And(s == 0, e == 0)))

# Pairwise non-overlap with travel time if both meetings selected
for i in range(len(people)):
    for j in range(i+1, len(people)):
        pi = people[i]
        pj = people[j]
        mi = meet_vars[pi["name"]]
        mj = meet_vars[pj["name"]]
        si = start_vars[pi["name"]]
        ei = end_vars[pi["name"]]
        sj = start_vars[pj["name"]]
        ej = end_vars[pj["name"]]
        tij = travel[pi["location"]][pj["location"]]
        tji = travel[pj["location"]][pi["location"]]
        opt.add(Implies(And(mi, mj), Or(ei + tij <= sj, ej + tji <= si)))

# Objectives
count_meetings = Sum([If(meet_vars[p["name"]], 1, 0) for p in people])
total_meeting_minutes = Sum([If(meet_vars[p["name"]], end_vars[p["name"]] - start_vars[p["name"]], 0) for p in people])

opt.maximize(count_meetings)
opt.maximize(total_meeting_minutes)

if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
else:
    model = opt.model()
    itinerary = []
    for p in people:
        name = p["name"]
        if is_true(model.evaluate(meet_vars[name])):  # only include met people
            s = model.evaluate(start_vars[name]).as_long()
            e = model.evaluate(end_vars[name]).as_long()
            itinerary.append({
                "action": "meet",
                "location": p["location"],
                "person": name,
                "start_time": minutes_to_str(s),
                "end_time": minutes_to_str(e)
            })
    # sort by start time
    itinerary.sort(key=lambda x: int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1]))
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))