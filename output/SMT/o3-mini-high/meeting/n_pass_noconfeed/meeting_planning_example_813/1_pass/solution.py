#!/usr/bin/env python3
import json
from z3 import *

# Travel times dictionary (in minutes)
travel = {
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Mission District"): 20,

    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Mission District"): 20,

    ("Bayview", "Marina District"): 27,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Mission District"): 13,

    ("Union Square", "Marina District"): 18,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Mission District"): 14,

    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Mission District"): 17,

    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Mission District"): 25,

    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,

    ("Financial District", "Marina District"): 15,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Mission District"): 17,

    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Mission District"): 11,

    ("Mission District", "Marina District"): 19,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Haight-Ashbury"): 12
}

# Friend meeting parameters.
# Times are expressed as minutes from midnight.
# Note: You arrive at "Marina District" at 9:00 (i.e. 540 minutes).
friends = [
    {"name": "Joshua", "location": "Embarcadero",   "avail_start": 585,  "avail_end": 1080, "min": 105},
    {"name": "Jeffrey", "location": "Bayview",       "avail_start": 585,  "avail_end": 1215, "min": 75},
    {"name": "Charles", "location": "Union Square",   "avail_start": 645,  "avail_end": 1215, "min": 120},
    {"name": "Joseph",  "location": "Chinatown",      "avail_start": 540,  "avail_end": 930,  "min": 60},
    {"name": "Elizabeth", "location": "Sunset District", "avail_start": 540, "avail_end": 585,  "min": 45},
    {"name": "Matthew", "location": "Golden Gate Park", "avail_start": 660, "avail_end": 1170, "min": 45},
    {"name": "Carol",   "location": "Financial District", "avail_start": 645, "avail_end": 675, "min": 15},
    {"name": "Paul",    "location": "Haight-Ashbury", "avail_start": 1155, "avail_end": 1230, "min": 15},
    {"name": "Rebecca", "location": "Mission District", "avail_start": 1020, "avail_end": 1305, "min": 45}
]

num_friends = len(friends)

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variables:
# s_vars[i] : meeting start time (in minutes, from midnight) for friend i.
# pos_vars[i] : integer representing the position in the day’s itinerary (0 means not scheduled).
# meet_vars[i] : Boolean variable; True if friend i is met.
s_vars = [Int(f"s_{i}") for i in range(num_friends)]
pos_vars = [Int(f"pos_{i}") for i in range(num_friends)]
meet_vars = [Bool(f"meet_{i}") for i in range(num_friends)]

# total_meetings: total number of meetings scheduled
total_meetings = Int("total_meetings")
opt.add(total_meetings == Sum([If(meet_vars[i], 1, 0) for i in range(num_friends)]))

# For each friend: if scheduled, meeting must occur within availability and have exactly the minimum duration.
for i in range(num_friends):
    f = friends[i]
    dur = f["min"]
    # When meeting is scheduled
    opt.add(Implies(meet_vars[i], s_vars[i] >= f["avail_start"]))
    opt.add(Implies(meet_vars[i], s_vars[i] + dur <= f["avail_end"]))
    # If scheduled, position must be between 1 and num_friends and at most total_meetings;
    # if not scheduled, position is 0.
    opt.add(If(meet_vars[i],
               And(pos_vars[i] >= 1, pos_vars[i] <= num_friends, pos_vars[i] <= total_meetings),
               pos_vars[i] == 0))

# Enforce that scheduled meetings get distinct positions.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Implies(And(meet_vars[i], meet_vars[j]), pos_vars[i] != pos_vars[j]))
# Ensure that if total_meetings is at least k then some meeting has position k.
for k in range(1, num_friends+1):
    opt.add(Implies(k <= total_meetings,
                    Or([And(meet_vars[i], pos_vars[i] == k) for i in range(num_friends)])))

# Ordering constraints:
# 1. For the first meeting (position 1), you must travel from Marina District starting at 9:00 (540).
for i in range(num_friends):
    req_time = 540 + travel[("Marina District", friends[i]["location"])]
    opt.add(Implies(And(meet_vars[i], pos_vars[i] == 1), s_vars[i] >= req_time))

# 2. For meetings beyond the first (position > 1), there must be a predecessor meeting
# that finishes (start + duration) and then you travel from that location.
for i in range(num_friends):
    # For each meeting i (with pos > 1) add: 
    # there exists some meeting j (j != i) such that j is scheduled and pos_i = pos_j + 1
    # and the start time of i respects the predecessor’s finish time plus travel time.
    pred_options = []
    for j in range(num_friends):
        if i != j:
            pred_options.append(And(
                meet_vars[j],
                pos_vars[i] == pos_vars[j] + 1,
                s_vars[i] >= s_vars[j] + friends[j]["min"] + travel[(friends[j]["location"], friends[i]["location"])]
            ))
    if pred_options:
        opt.add(Implies(And(meet_vars[i], pos_vars[i] > 1), Or(pred_options)))

# Objective: maximize total number of meetings scheduled.
opt.maximize(total_meetings)

# Check for a solution.
if opt.check() == sat:
    model = opt.model()
    # Gather scheduled meetings, along with their position, start, and end times.
    scheduled = []
    for i in range(num_friends):
        if is_true(model.eval(meet_vars[i])):
            pos_val = model.eval(pos_vars[i]).as_long()
            start_val = model.eval(s_vars[i]).as_long()
            end_val = start_val + friends[i]["min"]
            scheduled.append((pos_val, i, start_val, end_val))
    scheduled.sort(key=lambda x: x[0])
    
    def format_time(t):
        hour = t // 60
        minute = t % 60
        return f"{hour}:{minute:02d}"
    
    itinerary = []
    for pos_val, i, start_t, end_t in scheduled:
        itinerary.append({
            "action": "meet",
            "location": friends[i]["location"],
            "person": friends[i]["name"],
            "start_time": format_time(start_t),
            "end_time": format_time(end_t)
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"itinerary": []}))