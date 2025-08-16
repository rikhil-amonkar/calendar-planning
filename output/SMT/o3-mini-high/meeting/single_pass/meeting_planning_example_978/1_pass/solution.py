from z3 import *
import json

# All times are in minutes after midnight.
# For example, 9:00 AM = 9*60 = 540.
# Define travel times as provided.
travel = {
    "Embarcadero": {
        "Fisherman's Wharf": 6,
        "Financial District": 5,
        "Russian Hill": 8,
        "Marina District": 12,
        "Richmond District": 21,
        "Pacific Heights": 11,
        "Haight-Ashbury": 21,
        "Presidio": 20,
        "Nob Hill": 10,
        "The Castro": 25
    },
    "Fisherman's Wharf": {
        "Embarcadero": 8,
        "Financial District": 10,
        "Russian Hill": 7,
        "Marina District": 9,
        "Richmond District": 18,
        "Pacific Heights": 12,
        "Haight-Ashbury": 22,
        "Presidio": 17,
        "Nob Hill": 11,
        "The Castro": 27
    },
    "Financial District": {
        "Embarcadero": 4,
        "Fisherman's Wharf": 10,
        "Russian Hill": 11,
        "Marina District": 15,
        "Richmond District": 21,
        "Pacific Heights": 13,
        "Haight-Ashbury": 19,
        "Presidio": 22,
        "Nob Hill": 8,
        "The Castro": 20
    },
    "Russian Hill": {
        "Embarcadero": 8,
        "Fisherman's Wharf": 7,
        "Financial District": 11,
        "Marina District": 7,
        "Richmond District": 14,
        "Pacific Heights": 7,
        "Haight-Ashbury": 17,
        "Presidio": 14,
        "Nob Hill": 5,
        "The Castro": 21
    },
    "Marina District": {
        "Embarcadero": 14,
        "Fisherman's Wharf": 10,
        "Financial District": 17,
        "Russian Hill": 8,
        "Richmond District": 11,
        "Pacific Heights": 7,
        "Haight-Ashbury": 16,
        "Presidio": 10,
        "Nob Hill": 12,
        "The Castro": 22
    },
    "Richmond District": {
        "Embarcadero": 19,
        "Fisherman's Wharf": 18,
        "Financial District": 22,
        "Russian Hill": 13,
        "Marina District": 9,
        "Pacific Heights": 10,
        "Haight-Ashbury": 10,
        "Presidio": 7,
        "Nob Hill": 17,
        "The Castro": 16
    },
    "Pacific Heights": {
        "Embarcadero": 10,
        "Fisherman's Wharf": 13,
        "Financial District": 13,
        "Russian Hill": 7,
        "Marina District": 6,
        "Richmond District": 12,
        "Haight-Ashbury": 11,
        "Presidio": 11,
        "Nob Hill": 8,
        "The Castro": 16
    },
    "Haight-Ashbury": {
        "Embarcadero": 20,
        "Fisherman's Wharf": 23,
        "Financial District": 21,
        "Russian Hill": 17,
        "Marina District": 17,
        "Richmond District": 10,
        "Pacific Heights": 12,
        "Presidio": 15,
        "Nob Hill": 15,
        "The Castro": 6
    },
    "Presidio": {
        "Embarcadero": 20,
        "Fisherman's Wharf": 19,
        "Financial District": 23,
        "Russian Hill": 14,
        "Marina District": 11,
        "Richmond District": 7,
        "Pacific Heights": 11,
        "Haight-Ashbury": 15,
        "Nob Hill": 18,
        "The Castro": 21
    },
    "Nob Hill": {
        "Embarcadero": 9,
        "Fisherman's Wharf": 10,
        "Financial District": 9,
        "Russian Hill": 5,
        "Marina District": 11,
        "Richmond District": 14,
        "Pacific Heights": 8,
        "Haight-Ashbury": 13,
        "Presidio": 17,
        "The Castro": 17
    },
    "The Castro": {
        "Embarcadero": 22,
        "Fisherman's Wharf": 24,
        "Financial District": 21,
        "Russian Hill": 18,
        "Marina District": 21,
        "Richmond District": 16,
        "Pacific Heights": 16,
        "Haight-Ashbury": 6,
        "Presidio": 20,
        "Nob Hill": 16
    }
}

# Friend details:
# - Each friend is at a specific neighborhood.
# - Their availability window is given in minutes from midnight.
# - Minimum meeting durations are also in minutes.
friends = [
    {"name": "Stephanie", "location": "Fisherman's Wharf", "avail_start": 930, "avail_end": 1320, "min_duration": 30},
    {"name": "Lisa", "location": "Financial District", "avail_start": 645, "avail_end": 1035, "min_duration": 15},
    {"name": "Melissa", "location": "Russian Hill", "avail_start": 1020, "avail_end": 1305, "min_duration": 120},
    {"name": "Betty", "location": "Marina District", "avail_start": 645, "avail_end": 855, "min_duration": 60},
    {"name": "Sarah", "location": "Richmond District", "avail_start": 975, "avail_end": 1170, "min_duration": 105},
    {"name": "Daniel", "location": "Pacific Heights", "avail_start": 1110, "avail_end": 1305, "min_duration": 60},
    {"name": "Joshua", "location": "Haight-Ashbury", "avail_start": 540, "avail_end": 930, "min_duration": 15},
    {"name": "Joseph", "location": "Presidio", "avail_start": 420, "avail_end": 780, "min_duration": 45},
    {"name": "Andrew", "location": "Nob Hill", "avail_start": 1185, "avail_end": 1320, "min_duration": 105},
    {"name": "John", "location": "The Castro", "avail_start": 795, "avail_end": 1185, "min_duration": 45}
]

n = len(friends)
opt = Optimize()

# Create decision variables for each friend:
# s_vars[i]: meeting start time for friend i.
# e_vars[i]: meeting end time for friend i.
# sched[i]  : whether the meeting with friend i is scheduled.
s_vars = [Int(f"s_{i}") for i in range(n)]
e_vars = [Int(f"e_{i}") for i in range(n)]
sched = [Bool(f"sched_{i}") for i in range(n)]

# For each friend, if the meeting is scheduled the meeting must:
#  (1) start no earlier than the friend’s availability;
#  (2) finish no later than the friend’s availability;
#  (3) last at least the minimum required duration;
#  (4) and you must travel from your start point (Embarcadero at 9:00, i.e. 540)
#      to the friend’s location.
for i, friend in enumerate(friends):
    opt.add(Implies(sched[i], s_vars[i] >= friend["avail_start"]))
    opt.add(Implies(sched[i], e_vars[i] <= friend["avail_end"]))
    opt.add(Implies(sched[i], e_vars[i] - s_vars[i] >= friend["min_duration"]))
    travel_from_start = travel["Embarcadero"][friend["location"]]
    opt.add(Implies(sched[i], s_vars[i] >= 540 + travel_from_start))

# For meetings that are scheduled one after the other,
# we need to ensure that travel time from one friend’s location to the next is respected.
# For every pair of friends (i, j) (with i<j), introduce a boolean to decide who comes first.
order_vars = {}
for i in range(n):
    for j in range(i+1, n):
        order_var = Bool(f"order_{i}_{j}")
        order_vars[(i, j)] = order_var
        # If both meetings are scheduled and we decide friend i comes before friend j,
        # then the end of i plus travel time from i to j must be no later than the start time of j.
        travel_i_j = travel[friends[i]["location"]][friends[j]["location"]]
        travel_j_i = travel[friends[j]["location"]][friends[i]["location"]]
        opt.add(Implies(And(sched[i], sched[j], order_var),
                        e_vars[i] + travel_i_j <= s_vars[j]))
        # Otherwise (if j comes before i) enforce the reverse travel constraint.
        opt.add(Implies(And(sched[i], sched[j], Not(order_var)),
                        e_vars[j] + travel_j_i <= s_vars[i]))

# To enforce consistency in ordering among three meetings we add transitivity constraints.
# For any three friends i < j < k, if both i comes before j and j comes before k then i must come before k.
for i in range(n):
    for j in range(i+1, n):
        for k in range(j+1, n):
            opt.add(Implies(And(sched[i], sched[j], sched[k],
                                order_vars[(i, j)], order_vars[(j, k)]),
                            order_vars[(i, k)]))

# Our objective is to maximize the number of meetings (friends) scheduled.
total_meetings = Sum([If(sched[i], 1, 0) for i in range(n)])
opt.maximize(total_meetings)

# Try to solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    itinerary = []
    scheduled_meetings = []
    for i in range(n):
        if model.evaluate(sched[i]):
            st = model.evaluate(s_vars[i]).as_long()
            et = model.evaluate(e_vars[i]).as_long()
            scheduled_meetings.append((st, et, friends[i]["name"]))
    # Sort the meetings in chronological order.
    scheduled_meetings.sort(key=lambda x: x[0])
    
    # Helper function to convert minutes to "HH:MM" format.
    def minutes_to_HHMM(m):
        hh = m // 60
        mm = m % 60
        return f"{hh:02d}:{mm:02d}"
    
    for st, et, name in scheduled_meetings:
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": minutes_to_HHMM(st),
            "end_time": minutes_to_HHMM(et)
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")