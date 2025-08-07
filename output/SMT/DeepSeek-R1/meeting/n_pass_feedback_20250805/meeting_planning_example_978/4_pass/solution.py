from z3 import *
import json

# Define the travel_time_dict
travel_time_dict = {
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
        "Financial District": 11,
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

# Define friends with their details
friends = [
    ('Stephanie', "Fisherman's Wharf", (15*60+30, 22*60), 30),
    ('Lisa', "Financial District", (10*60+45, 17*60+15), 15),
    ('Melissa', "Russian Hill", (17*60, 21*60+45), 120),
    ('Betty', "Marina District", (10*60+45, 14*60+15), 60),
    ('Sarah', "Richmond District", (16*60+15, 19*60+30), 105),
    ('Daniel', "Pacific Heights", (18*60+30, 21*60+45), 60),
    ('Joshua', "Haight-Ashbury", (9*60, 15*60+30), 15),
    ('Joseph', "Presidio", (7*60, 13*60), 45),
    ('Andrew', "Nob Hill", (19*60+45, 22*60), 105),
    ('John', "The Castro", (13*60+15, 19*60+45), 45)
]

# Create Z3 Optimize solver
opt = Optimize()

# Variables
meet = [Bool(f'meet_{i}') for i in range(10)]
start = [Int(f'start_{i}') for i in range(10)]
end = [Int(f'end_{i}') for i in range(10)]
position = [Int(f'position_{i}') for i in range(10)]

# Friend details
locations = [f[1] for f in friends]
min_times = [f[3] for f in friends]
start_minutes = [f[2][0] for f in friends]
end_minutes = [f[2][1] for f in friends]

# Constraints for each friend
for i in range(10):
    opt.add(Implies(meet[i], start[i] >= start_minutes[i]))
    opt.add(Implies(meet[i], end[i] <= end_minutes[i]))
    opt.add(Implies(meet[i], end[i] - start[i] >= min_times[i]))
    opt.add(Implies(meet[i], position[i] >= 0))
    opt.add(Implies(meet[i], position[i] < 10))
    opt.add(Implies(Not(meet[i]), position[i] == -1))
    # Critical constraint: no meeting can start before 9:00 AM (540 minutes)
    opt.add(Implies(meet[i], start[i] >= 540))

# Distinct positions for met friends
for i in range(10):
    for j in range(i+1, 10):
        opt.add(Implies(And(meet[i], meet[j]), position[i] != position[j]))

# Position order must match start time order
for i in range(10):
    for j in range(10):
        if i == j:
            continue
        opt.add(Implies(And(meet[i], meet[j], position[i] < position[j]), start[i] < start[j]))

# Initial travel constraint: from Embarcadero to first meeting location
for i in range(10):
    opt.add(Implies(And(meet[i], position[i] == 0), 
                  start[i] >= 540 + travel_time_dict["Embarcadero"][locations[i]]))

# Travel time between consecutive meetings
for i in range(10):
    for j in range(10):
        if i == j:
            continue
        # We consider meetings i and j where i has a lower position than j
        opt.add(Implies(And(meet[i], meet[j], position[i] < position[j]),
                       start[j] >= end[i] + travel_time_dict[locations[i]][locations[j]]))

# Maximize the number of friends met
objective = Sum([If(meet[i], 1, 0) for i in range(10)])
opt.maximize(objective)

# Solve
if opt.check() == sat:
    model = opt.model()
    # Extract results
    itinerary = []
    for i in range(10):
        if model.evaluate(meet[i]):
            start_val = model.evaluate(start[i]).as_long()
            end_val = model.evaluate(end[i]).as_long()
            pos_val = model.evaluate(position[i]).as_long()
            # Convert minutes to HH:MM
            start_time = f"{start_val // 60:02d}:{start_val % 60:02d}"
            end_time = f"{end_val // 60:02d}:{end_val % 60:02d}"
            itinerary.append({
                "person": friends[i][0],
                "start": start_time,
                "end": end_time,
                "pos": pos_val
            })
    # Sort by position
    itinerary_sorted = sorted(itinerary, key=lambda x: x['pos'])
    # Format output
    result = [{"action": "meet", "person": item["person"], "start_time": item["start"], "end_time": item["end"]} for item in itinerary_sorted]
    output = {"itinerary": result}
    print("SOLUTION:")
    print(json.dumps(output, indent=2))
else:
    print("No solution found")