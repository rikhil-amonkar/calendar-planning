import json
from z3 import *

# Travel times data as a list of tuples (from, to, time)
travel_data = [
    ("Marina District", "Embarcadero", 14),
    ("Marina District", "Bayview", 27),
    ("Marina District", "Union Square", 16),
    ("Marina District", "Chinatown", 15),
    ("Marina District", "Sunset District", 19),
    ("Marina District", "Golden Gate Park", 18),
    ("Marina District", "Financial District", 17),
    ("Marina District", "Haight-Ashbury", 16),
    ("Marina District", "Mission District", 20),
    ("Embarcadero", "Marina District", 12),
    ("Embarcadero", "Bayview", 21),
    ("Embarcadero", "Union Square", 10),
    ("Embarcadero", "Chinatown", 7),
    ("Embarcadero", "Sunset District", 30),
    ("Embarcadero", "Golden Gate Park", 25),
    ("Embarcadero", "Financial District", 5),
    ("Embarcadero", "Haight-Ashbury", 21),
    ("Embarcadero", "Mission District", 20),
    ("Bayview", "Marina District", 27),
    ("Bayview", "Embarcadero", 19),
    ("Bayview", "Union Square", 18),
    ("Bayview", "Chinatown", 19),
    ("Bayview", "Sunset District", 23),
    ("Bayview", "Golden Gate Park", 22),
    ("Bayview", "Financial District", 19),
    ("Bayview", "Haight-Ashbury", 19),
    ("Bayview", "Mission District", 13),
    ("Union Square", "Marina District", 18),
    ("Union Square", "Embarcadero", 11),
    ("Union Square", "Bayview", 15),
    ("Union Square", "Chinatown", 7),
    ("Union Square", "Sunset District", 27),
    ("Union Square", "Golden Gate Park", 22),
    ("Union Square", "Financial District", 9),
    ("Union Square", "Haight-Ashbury", 18),
    ("Union Square", "Mission District", 14),
    ("Chinatown", "Marina District", 12),
    ("Chinatown", "Embarcadero", 5),
    ("Chinatown", "Bayview", 20),
    ("Chinatown", "Union Square", 7),
    ("Chinatown", "Sunset District", 29),
    ("Chinatown", "Golden Gate Park", 23),
    ("Chinatown", "Financial District", 5),
    ("Chinatown", "Haight-Ashbury", 19),
    ("Chinatown", "Mission District", 17),
    ("Sunset District", "Marina District", 21),
    ("Sunset District", "Embarcadero", 30),
    ("Sunset District", "Bayview", 22),
    ("Sunset District", "Union Square", 30),
    ("Sunset District", "Chinatown", 30),
    ("Sunset District", "Golden Gate Park", 11),
    ("Sunset District", "Financial District", 30),
    ("Sunset District", "Haight-Ashbury", 15),
    ("Sunset District", "Mission District", 25),
    ("Golden Gate Park", "Marina District", 16),
    ("Golden Gate Park", "Embarcadero", 25),
    ("Golden Gate Park", "Bayview", 23),
    ("Golden Gate Park", "Union Square", 22),
    ("Golden Gate Park", "Chinatown", 23),
    ("Golden Gate Park", "Sunset District", 10),
    ("Golden Gate Park", "Financial District", 26),
    ("Golden Gate Park", "Haight-Ashbury", 7),
    ("Golden Gate Park", "Mission District", 17),
    ("Financial District", "Marina District", 15),
    ("Financial District", "Embarcadero", 4),
    ("Financial District", "Bayview", 19),
    ("Financial District", "Union Square", 9),
    ("Financial District", "Chinatown", 5),
    ("Financial District", "Sunset District", 30),
    ("Financial District", "Golden Gate Park", 23),
    ("Financial District", "Haight-Ashbury", 19),
    ("Financial District", "Mission District", 17),
    ("Haight-Ashbury", "Marina District", 17),
    ("Haight-Ashbury", "Embarcadero", 20),
    ("Haight-Ashbury", "Bayview", 18),
    ("Haight-Ashbury", "Union Square", 19),
    ("Haight-Ashbury", "Chinatown", 19),
    ("Haight-Ashbury", "Sunset District", 15),
    ("Haight-Ashbury", "Golden Gate Park", 7),
    ("Haight-Ashbury", "Financial District", 21),
    ("Haight-Ashbury", "Mission District", 11),
    ("Mission District", "Marina District", 19),
    ("Mission District", "Embarcadero", 19),
    ("Mission District", "Bayview", 14),
    ("Mission District", "Union Square", 15),
    ("Mission District", "Chinatown", 16),
    ("Mission District", "Sunset District", 24),
    ("Mission District", "Golden Gate Park", 17),
    ("Mission District", "Financial District", 15),
    ("Mission District", "Haight-Ashbury", 12)
]

# Build travel dictionary
travel_dict = {}
for (src, dst, time_val) in travel_data:
    travel_dict[(src, dst)] = time_val

# Locations: index 0: Marina District (dummy meeting), then 1..9 for the friends
locations = [
    "Marina District",      # 0
    "Embarcadero",          # 1 Joshua
    "Bayview",              # 2 Jeffrey
    "Union Square",         # 3 Charles
    "Chinatown",            # 4 Joseph
    "Sunset District",      # 5 Elizabeth
    "Golden Gate Park",     # 6 Matthew
    "Financial District",   # 7 Carol
    "Haight-Ashbury",       # 8 Paul
    "Mission District"      # 9 Rebecca
]

# Friend names corresponding to indices 1 to 9
friend_names = {
    1: "Joshua",
    2: "Jeffrey",
    3: "Charles",
    4: "Joseph",
    5: "Elizabeth",
    6: "Matthew",
    7: "Carol",
    8: "Paul",
    9: "Rebecca"
}

# Availability and min_duration for friends (indices 1 to 9)
# [start_minutes, end_minutes, min_duration]
# Convert times to minutes from midnight
friend_data = {
    1: [9*60+45, 18*60, 105],      # Joshua: 9:45-18:00, 105 min
    2: [9*60+45, 20*60+15, 75],    # Jeffrey: 9:45-20:15, 75 min
    3: [10*60+45, 20*60+15, 120],  # Charles: 10:45-20:15, 120 min
    4: [7*60, 15*60+30, 60],       # Joseph: 7:00-15:30, 60 min
    5: [9*60, 9*60+45, 45],        # Elizabeth: 9:00-9:45, 45 min
    6: [11*60, 19*60+30, 45],      # Matthew: 11:00-19:30, 45 min
    7: [10*60+45, 11*60+15, 15],   # Carol: 10:45-11:15, 15 min
    8: [19*60+15, 20*60+30, 15],   # Paul: 19:15-20:30, 15 min
    9: [17*60, 21*60+45, 45]       # Rebecca: 17:00-21:45, 45 min
}

# Build travel time matrix between the 10 locations (index 0 to 9)
travel_matrix = [[0 for _ in range(10)] for _ in range(10)]
for i in range(10):
    for j in range(10):
        if i != j:
            travel_matrix[i][j] = travel_dict.get((locations[i], locations[j]), 0)

# Create Z3 optimizer
opt = Optimize()

# Number of meetings: 10 (0: dummy, 1..9: friends)
n = 10

# met[i]: whether we meet meeting i (0 is dummy and always met)
met = [Bool(f'met_{i}') for i in range(n)]
# For the dummy meeting (index0), we set met[0] to True
opt.add(met[0] == True)
# For friends (indices 1..9), met[i] is a variable

# start[i]: start time in minutes (from midnight)
start = [Int(f'start_{i}') for i in range(n)]
# Fix start[0] to 540 (9:00 AM)
opt.add(start[0] == 540)

# min_duration for each meeting
min_duration = [0] + [friend_data[i][2] for i in range(1, 10)]

# Define end time for each meeting
end = [start[i] + min_duration[i] for i in range(n)]

# Availability constraints for friends (indices 1 to 9)
for i in range(1, n):
    avail_start, avail_end, _ = friend_data[i]
    # If we meet the friend, then the start time must be within the availability window and the end time must not exceed the availability end
    opt.add(Implies(met[i], And(start[i] >= avail_start, end[i] <= avail_end)))

# Create before[i][j] for i, j in [0,9] and i != j
before = [[Bool(f'before_{i}_{j}') for j in range(n)] for i in range(n)]

# For each pair (i, j) with i != j, if both are met, then we have disjunctive constraints
for i in range(n):
    for j in range(n):
        if i != j:
            # If both meetings are met, then either i before j or j before i
            opt.add(Implies(And(met[i], met[j]), 
                          Or(before[i][j], before[j][i])))
            # Antisymmetry: if i before j then not j before i
            opt.add(Implies(before[i][j], Not(before[j][i])))
            # The disjunctive constraint for travel
            # If i before j is true, then start[j] >= end[i] + travel_time(i, j)
            opt.add(Implies(And(met[i], met[j], before[i][j]), 
                          start[j] >= end[i] + travel_matrix[i][j]))
            # Similarly, if j before i is true, then start[i] >= end[j] + travel_time(j, i)
            opt.add(Implies(And(met[i], met[j], before[j][i]), 
                          start[i] >= end[j] + travel_matrix[j][i]))

# Transitivity: for all distinct i, j, k, if i before j and j before k then i before k
for i in range(n):
    for j in range(n):
        if i != j:
            for k in range(n):
                if k != i and k != j:
                    opt.add(Implies(And(before[i][j], before[j][k]), before[i][k]))

# We also force that the dummy meeting (index0) is before every real meeting (if they are met)
for j in range(1, n):
    opt.add(Implies(met[j], before[0][j]))

# Objective: maximize the number of met friends (indices 1 to 9)
num_met = Sum([If(met[i], 1, 0) for i in range(1, n)])
opt.maximize(num_met)

# Solve
result = opt.check()
if result == sat:
    m = opt.model()
    # Extract the meetings that are met (for friends, indices 1 to 9)
    itinerary_entries = []
    for i in range(1, n):
        if is_true(m.eval(met[i])):
            start_val = m.eval(start[i]).as_long()
            # Convert minutes to HH:MM
            hours = start_val // 60
            minutes = start_val % 60
            start_str = f"{hours:02d}:{minutes:02d}"
            end_val = start_val + min_duration[i]
            hours_end = end_val // 60
            minutes_end = end_val % 60
            end_str = f"{hours_end:02d}:{minutes_end:02d}"
            itinerary_entries.append({
                "action": "meet",
                "person": friend_names[i],
                "start_time": start_str,
                "end_time": end_str
            })
    # Sort by start time
    itinerary_entries.sort(key=lambda x: x['start_time'])
    # Output as JSON
    output = {"itinerary": itinerary_entries}
    print("SOLUTION:")
    print(json.dumps(output, indent=2))
else:
    print("No solution found")