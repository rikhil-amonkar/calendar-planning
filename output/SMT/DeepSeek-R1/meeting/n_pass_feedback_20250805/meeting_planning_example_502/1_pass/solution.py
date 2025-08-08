import json
from z3 import *

# Travel time dictionary
travel_time_dict = {
    "Financial District": {
        "Golden Gate Park": 23,
        "Chinatown": 5,
        "Union Square": 9,
        "Fisherman's Wharf": 10,
        "North Beach": 7
    },
    "Golden Gate Park": {
        "Financial District": 26,
        "Chinatown": 23,
        "Union Square": 22,
        "Fisherman's Wharf": 24,
        "North Beach": 24
    },
    "Chinatown": {
        "Financial District": 5,
        "Golden Gate Park": 23,
        "Union Square": 7,
        "Fisherman's Wharf": 8,
        "North Beach": 3
    },
    "Union Square": {
        "Financial District": 9,
        "Golden Gate Park": 22,
        "Chinatown": 7,
        "Fisherman's Wharf": 15,
        "North Beach": 10
    },
    "Fisherman's Wharf": {
        "Financial District": 11,
        "Golden Gate Park": 25,
        "Chinatown": 12,
        "Union Square": 13,
        "North Beach": 6
    },
    "North Beach": {
        "Financial District": 8,
        "Golden Gate Park": 22,
        "Chinatown": 6,
        "Union Square": 7,
        "Fisherman's Wharf": 5
    }
}

# Friends data (excluding Joseph)
friends = [
    {"name": "Stephanie", "loc": "Golden Gate Park", "avail_start": 120, "avail_end": 360, "min_dur": 105},
    {"name": "Karen", "loc": "Chinatown", "avail_start": 285, "avail_end": 450, "min_dur": 15},
    {"name": "Brian", "loc": "Union Square", "avail_start": 360, "avail_end": 495, "min_dur": 30},
    {"name": "Rebecca", "loc": "Fisherman's Wharf", "avail_start": 0, "avail_end": 135, "min_dur": 30},
    {"name": "Steven", "loc": "North Beach", "avail_start": 330, "avail_end": 705, "min_dur": 120}
]

# Initialize Z3 solver
s = Optimize()

# Variables
meet = [Bool(f"meet_{i}") for i in range(5)]
start = [Int(f"start_{i}") for i in range(5)]

# Constraints for each friend
for i in range(5):
    s.add(Implies(meet[i], start[i] >= friends[i]["avail_start"]))
    s.add(Implies(meet[i], start[i] + friends[i]["min_dur"] <= friends[i]["avail_end"]))
    travel_from_start = travel_time_dict["Financial District"][friends[i]["loc"]]
    s.add(Implies(meet[i], start[i] >= travel_from_start))

# Pairwise constraints for every pair (i, j) with i < j
for i in range(5):
    for j in range(i+1, 5):
        before_ij = Bool(f"before_{i}_{j}")
        # If both meetings are held, enforce travel time based on order
        constraint = Or(
            And(before_ij, start[i] + friends[i]["min_dur"] + travel_time_dict[friends[i]["loc"]][friends[j]["loc"]] <= start[j]),
            And(Not(before_ij), start[j] + friends[j]["min_dur"] + travel_time_dict[friends[j]["loc"]][friends[i]["loc"]] <= start[i])
        )
        s.add(Implies(And(meet[i], meet[j]), constraint))

# Objective: maximize the number of meetings
objective = Sum([If(meet[i], 1, 0) for i in range(5)])
s.maximize(objective)

# Solve and extract itinerary
itinerary = []
if s.check() == sat:
    m = s.model()
    for i in range(5):
        if is_true(m.eval(meet[i])):
            start_val = m.eval(start[i])
            if is_int_value(start_val):
                start_minutes = start_val.as_long()
            else:
                start_minutes = start_val
            end_minutes = start_minutes + friends[i]["min_dur"]
            # Convert minutes to time string
            total_hours = 9 + (start_minutes // 60)
            total_minutes = start_minutes % 60
            start_time = f"{total_hours:02d}:{total_minutes:02d}"
            end_hours = 9 + (end_minutes // 60)
            end_minutes_remainder = end_minutes % 60
            end_time = f"{end_hours:02d}:{end_minutes_remainder:02d}"
            itinerary.append({
                "action": "meet",
                "person": friends[i]["name"],
                "start_time": start_time,
                "end_time": end_time
            })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x['start_time'])
    print('SOLUTION:')
    print(json.dumps({"itinerary": itinerary}))
else:
    print("SOLUTION:")
    print(json.dumps({"itinerary": []}))