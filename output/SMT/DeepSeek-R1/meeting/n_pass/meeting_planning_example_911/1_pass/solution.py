from z3 import *
import json

# Define locations
locations = [
    "The Castro",
    "North Beach",
    "Golden Gate Park",
    "Embarcadero",
    "Haight-Ashbury",
    "Richmond District",
    "Nob Hill",
    "Marina District",
    "Presidio",
    "Union Square",
    "Financial District"
]

# Travel times dictionary
travel_dict = {
    "The Castro": {
        "North Beach": 20,
        "Golden Gate Park": 11,
        "Embarcadero": 22,
        "Haight-Ashbury": 6,
        "Richmond District": 16,
        "Nob Hill": 16,
        "Marina District": 21,
        "Presidio": 20,
        "Union Square": 19,
        "Financial District": 21
    },
    "North Beach": {
        "The Castro": 23,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Haight-Ashbury": 18,
        "Richmond District": 18,
        "Nob Hill": 7,
        "Marina District": 9,
        "Presidio": 17,
        "Union Square": 7,
        "Financial District": 8
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "North Beach": 23,
        "Embarcadero": 25,
        "Haight-Ashbury": 7,
        "Richmond District": 7,
        "Nob Hill": 20,
        "Marina District": 16,
        "Presidio": 11,
        "Union Square": 22,
        "Financial District": 26
    },
    "Embarcadero": {
        "The Castro": 25,
        "North Beach": 5,
        "Golden Gate Park": 25,
        "Haight-Ashbury": 21,
        "Richmond District": 21,
        "Nob Hill": 10,
        "Marina District": 12,
        "Presidio": 20,
        "Union Square": 10,
        "Financial District": 5
    },
    "Haight-Ashbury": {
        "The Castro": 6,
        "North Beach": 19,
        "Golden Gate Park": 7,
        "Embarcadero": 20,
        "Richmond District": 10,
        "Nob Hill": 15,
        "Marina District": 17,
        "Presidio": 15,
        "Union Square": 19,
        "Financial District": 21
    },
    "Richmond District": {
        "The Castro": 16,
        "North Beach": 17,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Haight-Ashbury": 10,
        "Nob Hill": 17,
        "Marina District": 9,
        "Presidio": 7,
        "Union Square": 21,
        "Financial District": 22
    },
    "Nob Hill": {
        "The Castro": 17,
        "North Beach": 8,
        "Golden Gate Park": 17,
        "Embarcadero": 9,
        "Haight-Ashbury": 13,
        "Richmond District": 14,
        "Marina District": 11,
        "Presidio": 17,
        "Union Square": 7,
        "Financial District": 9
    },
    "Marina District": {
        "The Castro": 22,
        "North Beach": 11,
        "Golden Gate Park": 18,
        "Embarcadero": 14,
        "Haight-Ashbury": 16,
        "Richmond District": 11,
        "Nob Hill": 12,
        "Presidio": 10,
        "Union Square": 16,
        "Financial District": 17
    },
    "Presidio": {
        "The Castro": 21,
        "North Beach": 18,
        "Golden Gate Park": 12,
        "Embarcadero": 20,
        "Haight-Ashbury": 15,
        "Richmond District": 7,
        "Nob Hill": 18,
        "Marina District": 11,
        "Union Square": 22,
        "Financial District": 23
    },
    "Union Square": {
        "The Castro": 17,
        "North Beach": 10,
        "Golden Gate Park": 22,
        "Embarcadero": 11,
        "Haight-Ashbury": 18,
        "Richmond District": 20,
        "Nob Hill": 9,
        "Marina District": 18,
        "Presidio": 24,
        "Financial District": 9
    },
    "Financial District": {
        "The Castro": 20,
        "North Beach": 7,
        "Golden Gate Park": 23,
        "Embarcadero": 4,
        "Haight-Ashbury": 19,
        "Richmond District": 21,
        "Nob Hill": 8,
        "Marina District": 15,
        "Presidio": 22,
        "Union Square": 9
    }
}

# Create travel_time matrix: 11x11
travel_time = [[0] * 11 for _ in range(11)]
for i in range(11):
    from_loc = locations[i]
    for j in range(11):
        to_loc = locations[j]
        if i == j:
            travel_time[i][j] = 0
        else:
            travel_time[i][j] = travel_dict[from_loc][to_loc]

# Availability and min_duration
# Index 0: virtual (not used for availability)
avail_start = [0] * 11
avail_end = [0] * 11
min_dur = [0] * 11

# Steven (1)
avail_start[1] = 17*60+30  # 17:30
avail_end[1] = 20*60+30    # 20:30
min_dur[1] = 15

# Sarah (2)
avail_start[2] = 17*60      # 17:00
avail_end[2] = 19*60+15    # 19:15
min_dur[2] = 75

# Brian (3)
avail_start[3] = 14*60+15  # 14:15
avail_end[3] = 16*60       # 16:00
min_dur[3] = 105

# Stephanie (4)
avail_start[4] = 10*60+15  # 10:15
avail_end[4] = 12*60+15    # 12:15
min_dur[4] = 75

# Melissa (5)
avail_start[5] = 14*60     # 14:00
avail_end[5] = 19*60+30    # 19:30
min_dur[5] = 30

# Nancy (6)
avail_start[6] = 8*60+15   # 8:15
avail_end[6] = 12*60+45    # 12:45
min_dur[6] = 90

# David (7)
avail_start[7] = 11*60+15  # 11:15
avail_end[7] = 13*60+15    # 13:15
min_dur[7] = 120

# James (8)
avail_start[8] = 15*60     # 15:00
avail_end[8] = 18*60+15    # 18:15
min_dur[8] = 120

# Elizabeth (9)
avail_start[9] = 11*60+30  # 11:30
avail_end[9] = 21*60       # 21:00
min_dur[9] = 60

# Robert (10)
avail_start[10] = 13*60+15 # 13:15
avail_end[10] = 15*60+15   # 15:15
min_dur[10] = 45

# Create Z3 variables
meet = [Bool(f"meet_{i}") for i in range(11)]
start = [Int(f"start_{i}") for i in range(11)]
end = [Int(f"end_{i}") for i in range(11)]
position = [Int(f"position_{i}") for i in range(11)]

solver = Solver()
opt = Optimize()

# Virtual meeting (The Castro at 9:00 AM)
solver.add(meet[0] == True)
solver.add(start[0] == 540)  # 9:00 AM in minutes
solver.add(end[0] == 540)
solver.add(position[0] == 0)

# Constraints for each friend (index 1 to 10)
for i in range(1, 11):
    # If meeting i is scheduled, then:
    # 1. Start time >= availability start
    # 2. End time = start time + min duration
    # 3. End time <= availability end
    # 4. Position between 1 and 10
    solver.add(Implies(meet[i], start[i] >= avail_start[i]))
    solver.add(Implies(meet[i], end[i] == start[i] + min_dur[i]))
    solver.add(Implies(meet[i], end[i] <= avail_end[i]))
    solver.add(Implies(meet[i], position[i] >= 1))
    solver.add(Implies(meet[i], position[i] <= 10))

# Constraints for every pair of meetings (including virtual)
for i in range(11):
    for j in range(11):
        if i == j:
            continue
        both_meet = And(meet[i], meet[j])
        # Case 1: i before j
        case1 = And(position[i] < position[j], start[j] >= end[i] + travel_time[i][j])
        # Case 2: j before i
        case2 = And(position[j] < position[i], start[i] >= end[j] + travel_time[j][i])
        solver.add(Implies(both_meet, Or(case1, case2)))

# Distinct positions for meetings that are scheduled
for i in range(11):
    for j in range(i+1, 11):
        solver.add(Implies(And(meet[i], meet[j]), position[i] != position[j]))

# Objective: maximize the number of friends met
objective = Sum([If(meet[i], 1, 0) for i in range(1, 11)])
opt.add(solver.assertions())
opt.maximize(objective)

# Solve
if opt.check() == sat:
    model = opt.model()
    itinerary = []
    friends = [
        "Steven", "Sarah", "Brian", "Stephanie", "Melissa",
        "Nancy", "David", "James", "Elizabeth", "Robert"
    ]
    for idx in range(1, 11):
        if model.evaluate(meet[idx]):
            start_val = model.evaluate(start[idx])
            end_val = model.evaluate(end[idx])
            start_min = start_val.as_long()
            end_min = end_val.as_long()
            start_hour = start_min // 60
            start_minute = start_min % 60
            end_hour = end_min // 60
            end_minute = end_min % 60
            start_time = f"{start_hour:02d}:{start_minute:02d}"
            end_time = f"{end_hour:02d}:{end_minute:02d}"
            itinerary.append({
                "action": "meet",
                "person": friends[idx-1],
                "start_time": start_time,
                "end_time": end_time
            })
    # Sort itinerary by start time
    itinerary_sorted = sorted(itinerary, key=lambda x: x['start_time'])
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary_sorted}, indent=2))
else:
    print("SOLUTION:")
    print(json.dumps({"itinerary": []}))