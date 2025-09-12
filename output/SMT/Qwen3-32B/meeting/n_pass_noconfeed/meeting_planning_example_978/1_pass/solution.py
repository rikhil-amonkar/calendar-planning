import json
from z3 import *

# Define locations and their indices
locations = [
    "Embarcadero",
    "Fisherman's Wharf",
    "Financial District",
    "Russian Hill",
    "Marina District",
    "Richmond District",
    "Pacific Heights",
    "Haight-Ashbury",
    "Presidio",
    "Nob Hill",
    "The Castro"
]
loc_to_idx = {loc: idx for idx, loc in enumerate(locations)}

# Parse travel times
travel_times = {}

# Embarcadero to others
travel_times[("Embarcadero", "Fisherman's Wharf")] = 6
travel_times[("Embarcadero", "Financial District")] = 5
travel_times[("Embarcadero", "Russian Hill")] = 8
travel_times[("Embarcadero", "Marina District")] = 12
travel_times[("Embarcadero", "Richmond District")] = 21
travel_times[("Embarcadero", "Pacific Heights")] = 11
travel_times[("Embarcadero", "Haight-Ashbury")] = 21
travel_times[("Embarcadero", "Presidio")] = 20
travel_times[("Embarcadero", "Nob Hill")] = 10
travel_times[("Embarcadero", "The Castro")] = 25

# Fisherman's Wharf to others
travel_times[("Fisherman's Wharf", "Embarcadero")] = 8
travel_times[("Fisherman's Wharf", "Financial District")] = 11
travel_times[("Fisherman's Wharf", "Russian Hill")] = 7
travel_times[("Fisherman's Wharf", "Marina District")] = 9
travel_times[("Fisherman's Wharf", "Richmond District")] = 18
travel_times[("Fisherman's Wharf", "Pacific Heights")] = 12
travel_times[("Fisherman's Wharf", "Haight-Ashbury")] = 22
travel_times[("Fisherman's Wharf", "Presidio")] = 17
travel_times[("Fisherman's Wharf", "Nob Hill")] = 11
travel_times[("Fisherman's Wharf", "The Castro")] = 27

# Financial District to others
travel_times[("Financial District", "Embarcadero")] = 4
travel_times[("Financial District", "Fisherman's Wharf")] = 10
travel_times[("Financial District", "Russian Hill")] = 11
travel_times[("Financial District", "Marina District")] = 15
travel_times[("Financial District", "Richmond District")] = 21
travel_times[("Financial District", "Pacific Heights")] = 13
travel_times[("Financial District", "Haight-Ashbury")] = 19
travel_times[("Financial District", "Presidio")] = 22
travel_times[("Financial District", "Nob Hill")] = 8
travel_times[("Financial District", "The Castro")] = 20

# Russian Hill to others
travel_times[("Russian Hill", "Embarcadero")] = 8
travel_times[("Russian Hill", "Fisherman's Wharf")] = 7
travel_times[("Russian Hill", "Financial District")] = 11
travel_times[("Russian Hill", "Marina District")] = 7
travel_times[("Russian Hill", "Richmond District")] = 14
travel_times[("Russian Hill", "Pacific Heights")] = 7
travel_times[("Russian Hill", "Haight-Ashbury")] = 17
travel_times[("Russian Hill", "Presidio")] = 14
travel_times[("Russian Hill", "Nob Hill")] = 5
travel_times[("Russian Hill", "The Castro")] = 21

# Marina District to others
travel_times[("Marina District", "Embarcadero")] = 14
travel_times[("Marina District", "Fisherman's Wharf")] = 10
travel_times[("Marina District", "Financial District")] = 17
travel_times[("Marina District", "Russian Hill")] = 8
travel_times[("Marina District", "Richmond District")] = 11
travel_times[("Marina District", "Pacific Heights")] = 7
travel_times[("Marina District", "Haight-Ashbury")] = 16
travel_times[("Marina District", "Presidio")] = 10
travel_times[("Marina District", "Nob Hill")] = 12
travel_times[("Marina District", "The Castro")] = 22

# Richmond District to others
travel_times[("Richmond District", "Embarcadero")] = 19
travel_times[("Richmond District", "Fisherman's Wharf")] = 18
travel_times[("Richmond District", "Financial District")] = 22
travel_times[("Richmond District", "Russian Hill")] = 13
travel_times[("Richmond District", "Marina District")] = 9
travel_times[("Richmond District", "Pacific Heights")] = 10
travel_times[("Richmond District", "Haight-Ashbury")] = 10
travel_times[("Richmond District", "Presidio")] = 7
travel_times[("Richmond District", "Nob Hill")] = 17
travel_times[("Richmond District", "The Castro")] = 16

# Pacific Heights to others
travel_times[("Pacific Heights", "Embarcadero")] = 10
travel_times[("Pacific Heights", "Fisherman's Wharf")] = 13
travel_times[("Pacific Heights", "Financial District")] = 13
travel_times[("Pacific Heights", "Russian Hill")] = 7
travel_times[("Pacific Heights", "Marina District")] = 6
travel_times[("Pacific Heights", "Richmond District")] = 12
travel_times[("Pacific Heights", "Haight-Ashbury")] = 11
travel_times[("Pacific Heights", "Presidio")] = 11
travel_times[("Pacific Heights", "Nob Hill")] = 8
travel_times[("Pacific Heights", "The Castro")] = 16

# Haight-Ashbury to others
travel_times[("Haight-Ashbury", "Embarcadero")] = 20
travel_times[("Haight-Ashbury", "Fisherman's Wharf")] = 23
travel_times[("Haight-Ashbury", "Financial District")] = 21
travel_times[("Haight-Ashbury", "Russian Hill")] = 17
travel_times[("Haight-Ashbury", "Marina District")] = 17
travel_times[("Haight-Ashbury", "Richmond District")] = 10
travel_times[("Haight-Ashbury", "Pacific Heights")] = 12
travel_times[("Haight-Ashbury", "Presidio")] = 15
travel_times[("Haight-Ashbury", "Nob Hill")] = 15
travel_times[("Haight-Ashbury", "The Castro")] = 6

# Presidio to others
travel_times[("Presidio", "Embarcadero")] = 20
travel_times[("Presidio", "Fisherman's Wharf")] = 19
travel_times[("Presidio", "Financial District")] = 23
travel_times[("Presidio", "Russian Hill")] = 14
travel_times[("Presidio", "Marina District")] = 11
travel_times[("Presidio", "Richmond District")] = 7
travel_times[("Presidio", "Pacific Heights")] = 11
travel_times[("Presidio", "Haight-Ashbury")] = 15
travel_times[("Presidio", "Nob Hill")] = 18
travel_times[("Presidio", "The Castro")] = 21

# Nob Hill to others
travel_times[("Nob Hill", "Embarcadero")] = 9
travel_times[("Nob Hill", "Fisherman's Wharf")] = 10
travel_times[("Nob Hill", "Financial District")] = 9
travel_times[("Nob Hill", "Russian Hill")] = 5
travel_times[("Nob Hill", "Marina District")] = 11
travel_times[("Nob Hill", "Richmond District")] = 14
travel_times[("Nob Hill", "Pacific Heights")] = 8
travel_times[("Nob Hill", "Haight-Ashbury")] = 13
travel_times[("Nob Hill", "Presidio")] = 17
travel_times[("Nob Hill", "The Castro")] = 17

# The Castro to others
travel_times[("The Castro", "Embarcadero")] = 22
travel_times[("The Castro", "Fisherman's Wharf")] = 24
travel_times[("The Castro", "Financial District")] = 21
travel_times[("The Castro", "Russian Hill")] = 18
travel_times[("The Castro", "Marina District")] = 21
travel_times[("The Castro", "Richmond District")] = 16
travel_times[("The Castro", "Pacific Heights")] = 16
travel_times[("The Castro", "Haight-Ashbury")] = 6
travel_times[("The Castro", "Presidio")] = 20
travel_times[("The Castro", "Nob Hill")] = 16

# Build travel_time_matrix
num_locs = len(locations)
travel_time_matrix = [[0]*num_locs for _ in range(num_locs)]
for i in range(num_locs):
    for j in range(num_locs):
        from_loc = locations[i]
        to_loc = locations[j]
        travel_time_matrix[i][j] = travel_times.get( (from_loc, to_loc), 0 )

# Define people data
people = [
    {
        'name': 'Stephanie',
        'location': "Fisherman's Wharf",
        'available_start': 930,  # 3:30 PM
        'available_end': 1140,   # 10:00 PM
        'min_duration': 30
    },
    {
        'name': 'Lisa',
        'location': "Financial District",
        'available_start': 645,  # 10:45 AM
        'available_end': 1095,   # 5:15 PM
        'min_duration': 15
    },
    {
        'name': 'Melissa',
        'location': "Russian Hill",
        'available_start': 1020, # 5:00 PM
        'available_end': 1185,   # 9:45 PM
        'min_duration': 120
    },
    {
        'name': 'Betty',
        'location': "Marina District",
        'available_start': 645,  # 10:45 AM
        'available_end': 795,    # 2:15 PM
        'min_duration': 60
    },
    {
        'name': 'Sarah',
        'location': "Richmond District",
        'available_start': 975,  # 4:15 PM
        'available_end': 1170,   # 7:30 PM
        'min_duration': 105
    },
    {
        'name': 'Daniel',
        'location': "Pacific Heights",
        'available_start': 1110, # 6:30 PM
        'available_end': 1305,   # 9:45 PM
        'min_duration': 60
    },
    {
        'name': 'Joshua',
        'location': "Haight-Ashbury",
        'available_start': 540,  # 9:00 AM
        'available_end': 930,    # 3:30 PM
        'min_duration': 15
    },
    {
        'name': 'Joseph',
        'location': "Presidio",
        'available_start': 420,  # 7:00 AM
        'available_end': 780,    # 1:00 PM
        'min_duration': 45
    },
    {
        'name': 'Andrew',
        'location': "Nob Hill",
        'available_start': 1185, # 7:45 PM
        'available_end': 1320,   # 10:00 PM
        'min_duration': 105
    },
    {
        'name': 'John',
        'location': "The Castro",
        'available_start': 795,  # 1:15 PM
        'available_end': 1185,   # 7:45 PM
        'min_duration': 45
    }
]

num_people = len(people)

# Create Z3 solver
s = Optimize()

# Include variables
include = [Bool('include_{}'.format(i)) for i in range(num_people)]

# Start and end times for each person
start_p = [Int('start_p_{}'.format(i)) for i in range(num_people)]
end_p = [Int('end_p_{}'.format(i)) for i in range(num_people)]

# Add constraints for each person
for i in range(num_people):
    p = people[i]
    loc_idx = loc_to_idx[p['location']]
    # Available time constraints
    s.add(Implies(include[i], start_p[i] >= p['available_start']))
    s.add(Implies(include[i], end_p[i] == start_p[i] + p['min_duration']))
    s.add(Implies(include[i], end_p[i] <= p['available_end']))
    # First meeting must start after arrival + travel time from Embarcadero
    travel_time = travel_time_matrix[0][loc_idx]
    s.add(Implies(include[i], start_p[i] >= 540 + travel_time))

# Before variables for ordering
before = [[Bool('before_{}_{}'.format(i, j)) for j in range(num_people)] for i in range(num_people)]

for i in range(num_people):
    for j in range(i+1, num_people):
        # If both are included, then before[i][j] or before[j][i]
        s.add(Implies(And(include[i], include[j]), Or(before[i][j], before[j][i])))

        # If before[i][j], then end_p[i] + travel_time from i to j <= start_p[j]
        loc_i = loc_to_idx[people[i]['location']]
        loc_j = loc_to_idx[people[j]['location']]
        travel_time = travel_time_matrix[loc_i][loc_j]
        s.add(Implies(And(include[i], include[j], before[i][j]), start_p[j] >= end_p[i] + travel_time))

        # If before[j][i], then end_p[j] + travel_time from j to i <= start_p[i]
        travel_time_rev = travel_time_matrix[loc_j][loc_i]
        s.add(Implies(And(include[j], include[i], before[j][i]), start_p[i] >= end_p[j] + travel_time_rev))

# Objective: maximize the number of included people
obj = Sum([If(include[i], 1, 0) for i in range(num_people)])
s.maximize(obj)

# Solve
if s.check() == sat:
    model = s.model()
    included = [i for i in range(num_people) if model.evaluate(include[i])]
    itinerary = []
    for i in included:
        start_time = model.evaluate(start_p[i]).as_long()
        end_time = model.evaluate(end_p[i]).as_long()
        name = people[i]['name']
        location = people[i]['location']
        def to_time_str(m):
            h = m // 60
            mm = m % 60
            return f"{h}:{mm:02d}"
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": name,
            "start_time": to_time_str(start_time),
            "end_time": to_time_str(end_time)
        })
    # Sort by start_time
    itinerary.sort(key=lambda x: x['start_time'])
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print(json.dumps({"itinerary": []}))