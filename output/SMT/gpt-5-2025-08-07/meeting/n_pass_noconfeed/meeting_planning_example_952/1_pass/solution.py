# SOLUTION:
# This script computes an optimal meeting itinerary using Z3 SMT solver.

import json
from z3 import Int, Bool, And, Or, Implies, Optimize, If, Sum, sat

def t(h, m):
    return h*60 + m

def fmt(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

# Travel times (minutes) - directed
travel = {
    "Bayview": {
        "North Beach": 22, "Fisherman's Wharf": 25, "Haight-Ashbury": 19, "Nob Hill": 20,
        "Golden Gate Park": 22, "Union Square": 18, "Alamo Square": 16, "Presidio": 32,
        "Chinatown": 19, "Pacific Heights": 23
    },
    "North Beach": {
        "Bayview": 25, "Fisherman's Wharf": 5, "Haight-Ashbury": 18, "Nob Hill": 7,
        "Golden Gate Park": 22, "Union Square": 7, "Alamo Square": 16, "Presidio": 17,
        "Chinatown": 6, "Pacific Heights": 8
    },
    "Fisherman's Wharf": {
        "Bayview": 26, "North Beach": 6, "Haight-Ashbury": 22, "Nob Hill": 11,
        "Golden Gate Park": 25, "Union Square": 13, "Alamo Square": 21, "Presidio": 17,
        "Chinatown": 12, "Pacific Heights": 12
    },
    "Haight-Ashbury": {
        "Bayview": 18, "North Beach": 19, "Fisherman's Wharf": 23, "Nob Hill": 15,
        "Golden Gate Park": 7, "Union Square": 19, "Alamo Square": 5, "Presidio": 15,
        "Chinatown": 19, "Pacific Heights": 12
    },
    "Nob Hill": {
        "Bayview": 19, "North Beach": 8, "Fisherman's Wharf": 10, "Haight-Ashbury": 13,
        "Golden Gate Park": 17, "Union Square": 7, "Alamo Square": 11, "Presidio": 17,
        "Chinatown": 6, "Pacific Heights": 8
    },
    "Golden Gate Park": {
        "Bayview": 23, "North Beach": 23, "Fisherman's Wharf": 24, "Haight-Ashbury": 7,
        "Nob Hill": 20, "Union Square": 22, "Alamo Square": 9, "Presidio": 11,
        "Chinatown": 23, "Pacific Heights": 16
    },
    "Union Square": {
        "Bayview": 15, "North Beach": 10, "Fisherman's Wharf": 15, "Haight-Ashbury": 18,
        "Nob Hill": 9, "Golden Gate Park": 22, "Alamo Square": 14, "Presidio": 24,
        "Chinatown": 7, "Pacific Heights": 15
    },
    "Alamo Square": {
        "Bayview": 16, "North Beach": 15, "Fisherman's Wharf": 19, "Haight-Ashbury": 5,
        "Nob Hill": 11, "Golden Gate Park": 9, "Union Square": 14, "Presidio": 17,
        "Chinatown": 15, "Pacific Heights": 10
    },
    "Presidio": {
        "Bayview": 31, "North Beach": 18, "Fisherman's Wharf": 19, "Haight-Ashbury": 15,
        "Nob Hill": 18, "Golden Gate Park": 12, "Union Square": 22, "Alamo Square": 19,
        "Chinatown": 21, "Pacific Heights": 11
    },
    "Chinatown": {
        "Bayview": 20, "North Beach": 3, "Fisherman's Wharf": 8, "Haight-Ashbury": 19,
        "Nob Hill": 9, "Golden Gate Park": 23, "Union Square": 7, "Alamo Square": 17,
        "Presidio": 19, "Pacific Heights": 10
    },
    "Pacific Heights": {
        "Bayview": 22, "North Beach": 9, "Fisherman's Wharf": 13, "Haight-Ashbury": 11,
        "Nob Hill": 8, "Golden Gate Park": 15, "Union Square": 12, "Alamo Square": 10,
        "Presidio": 11, "Chinatown": 11
    }
}

# People data: name -> dict with location, availability window, min duration
people = {
    "Brian":    {"location": "North Beach",       "start": t(13, 0),  "end": t(19, 0),  "min_dur": 90},
    "Richard":  {"location": "Fisherman's Wharf", "start": t(11, 0),  "end": t(12, 45), "min_dur": 60},
    "Ashley":   {"location": "Haight-Ashbury",    "start": t(15, 0),  "end": t(20, 30), "min_dur": 90},
    "Elizabeth":{"location": "Nob Hill",          "start": t(11, 45), "end": t(18, 30), "min_dur": 75},
    "Jessica":  {"location": "Golden Gate Park",  "start": t(20, 0),  "end": t(21, 45), "min_dur": 105},
    "Deborah":  {"location": "Union Square",      "start": t(17, 30), "end": t(22, 0),  "min_dur": 60},
    "Kimberly": {"location": "Alamo Square",      "start": t(17, 30), "end": t(21, 15), "min_dur": 45},
    "Matthew":  {"location": "Presidio",          "start": t(8, 15),  "end": t(9, 0),   "min_dur": 15},
    "Kenneth":  {"location": "Chinatown",         "start": t(13, 45), "end": t(19, 30), "min_dur": 105},
    "Anthony":  {"location": "Pacific Heights",   "start": t(14, 15), "end": t(16, 0),  "min_dur": 30}
}

start_location = "Bayview"
arrive_time = t(9, 0)

# Build Z3 model
opt = Optimize()

# Variables
start_vars = {}
dur_vars = {}
end_vars = {}
meet_vars = {}

for person, info in people.items():
    s = Int(f"start_{person}")
    d = Int(f"dur_{person}")
    e = Int(f"end_{person}")
    m = Bool(f"meet_{person}")
    start_vars[person] = s
    dur_vars[person] = d
    end_vars[person] = e
    meet_vars[person] = m

    # Basic bounds
    opt.add(s >= 0, s <= 24*60)
    opt.add(d >= 0, d <= 24*60)
    opt.add(e == s + d)

    # Availability and minimum duration when meeting
    a_start = info["start"]
    a_end = info["end"]
    min_dur = info["min_dur"]

    opt.add(Implies(m, And(s >= a_start, e <= a_end, d >= min_dur)))
    # If not meeting, duration is zero
    opt.add(Implies(~m, d == 0))

    # Base travel from start location at arrival time
    loc = info["location"]
    base_travel = travel[start_location][loc]
    opt.add(Implies(m, s >= arrive_time + base_travel))

# Pairwise non-overlap with travel times
persons = list(people.keys())
for i in range(len(persons)):
    for j in range(i+1, len(persons)):
        pi = persons[i]
        pj = persons[j]
        li = people[pi]["location"]
        lj = people[pj]["location"]
        ti_to_j = travel[li][lj]
        tj_to_i = travel[lj][li]
        ei = end_vars[pi]
        ej = end_vars[pj]
        si = start_vars[pi]
        sj = start_vars[pj]
        mi = meet_vars[pi]
        mj = meet_vars[pj]
        opt.add(Implies(And(mi, mj), Or(ei + ti_to_j <= sj, ej + tj_to_i <= si)))

# Objectives: maximize number of meetings; then maximize total meeting time
num_meetings = Sum([If(meet_vars[p], 1, 0) for p in persons])
total_meeting_time = Sum([dur_vars[p] for p in persons])
opt.maximize(num_meetings)
opt.maximize(total_meeting_time)

# Solve
if opt.check() != sat:
    # Fallback empty itinerary (shouldn't happen)
    output = {"itinerary": []}
    print(json.dumps(output))
else:
    model = opt.model()
    # Build itinerary from model
    schedule = []
    for person in persons:
        if model.evaluate(meet_vars[person], model_completion=True):
            s = model.evaluate(start_vars[person]).as_long()
            e = model.evaluate(end_vars[person]).as_long()
            schedule.append({
                "action": "meet",
                "location": people[person]["location"],
                "person": person,
                "start": s,
                "end": e
            })

    # Sort by start time
    schedule.sort(key=lambda x: x["start"])

    # Format times and keys
    itinerary = []
    for item in schedule:
        itinerary.append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": fmt(item["start"]),
            "end_time": fmt(item["end"])
        })

    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))