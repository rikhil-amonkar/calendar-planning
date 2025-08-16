from z3 import *

# Define friends and their data
friends = [
    {
        'name': 'Elizabeth',
        'location': 'Financial District',
        'available_start': 60,  # 10:00AM in minutes since 9:00AM
        'available_end': 165,   # 12:45PM
        'duration': 75,
    },
    {
        'name': 'Joseph',
        'location': 'Union Square',
        'available_start': 75,  # 11:45AM
        'available_end': 165,   # 2:45PM
        'duration': 120,
    },
    {
        'name': 'Ashley',
        'location': 'Russian Hill',
        'available_start': 90,  # 11:30AM
        'available_end': 870,   # 9:30PM
        'duration': 45,
    },
    {
        'name': 'Karen',
        'location': 'Mission District',
        'available_start': 315, # 2:15PM
        'available_end': 600,   # 10:00PM
        'duration': 30,
    },
    {
        'name': 'Richard',
        'location': 'Fisherman's Wharf',
        'available_start': 330, # 2:30PM
        'available_end': 510,   # 5:30PM
        'duration': 30,
    },
    {
        'name': 'Helen',
        'location': 'Sunset District',
        'available_start': 345, # 2:45PM
        'available_end': 705,   # 8:45PM
        'duration': 105,
    },
    {
        'name': 'Kimberly',
        'location': 'Haight-Ashbury',
        'available_start': 315, # 2:15PM
        'available_end': 510,   # 5:30PM
        'duration': 105,
    },
    {
        'name': 'Robert',
        'location': 'Presidio',
        'available_start': 885, # 9:45PM
        'available_end': 945,   # 10:45PM
        'duration': 60,
    },
]

# Travel times between locations (in minutes)
travel_times = {
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Fisherman's Wharf'): 10,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Russian Hill'): 8,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'Fisherman's Wharf'): 22,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Financial District'): 15,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Russian Hill'): 15,
    ('Fisherman's Wharf', 'Marina District'): 9,
    ('Fisherman's Wharf', 'Mission District'): 22,
    ('Fisherman's Wharf', 'Presidio'): 17,
    ('Fisherman's Wharf', 'Union Square'): 13,
    ('Fisherman's Wharf', 'Sunset District'): 27,
    ('Fisherman's Wharf', 'Financial District'): 10,
    ('Fisherman's Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman's Wharf', 'Russian Hill'): 7,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Fisherman's Wharf'): 19,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Russian Hill'): 14,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Fisherman's Wharf'): 15,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Russian Hill'): 13,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Mission District'): 25,
    ('Sunset District', 'Fisherman's Wharf'): 29,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Russian Hill'): 24,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Mission District'): 17,
    ('Financial District', 'Fisherman's Wharf'): 10,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Russian Hill'): 11,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Fisherman's Wharf'): 23,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Fisherman's Wharf'): 7,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Haight-Ashbury'): 17,
}

num_friends = len(friends)
max_positions = 8

# Create sequence variables
seq = [Int(f'seq_{i}') for i in range(max_positions)]

# Create start and end time variables for each position
start = [Int(f'start_{i}') for i in range(max_positions)]
end = [Int(f'end_{i}') for i in range(max_positions)]

# Solver
s = Optimize()

# Constraints for sequence:
# 1. Each position is between 0 and num_friends-1
for i in range(max_positions):
    s.add(And(seq[i] >= 0, seq[i] <= num_friends - 1))

# 2. No duplicate friends in the sequence
for i in range(max_positions):
    for j in range(i + 1, max_positions):
        s.add(Implies(And(seq[i] > 0, seq[j] > 0), seq[i] != seq[j]))

# 3. For each position, if it's a friend, then start and end times are constrained
for i in range(max_positions):
    for fid in range(num_friends):
        loc = friends[fid]['location']
        available_start = friends[fid]['available_start']
        available_end = friends[fid]['available_end']
        duration = friends[fid]['duration']
        cond = (seq[i] == fid)
        s.add(Implies(cond, start[i] >= available_start))
        s.add(Implies(cond, end[i] == start[i] + duration))
        s.add(Implies(cond, end[i] <= available_end))

# 4. First position: start time >= travel time from Marina to location
for fid in range(num_friends):
    loc = friends[fid]['location']
    travel_time = travel_times[('Marina District', loc)]
    cond = (seq[0] == fid)
    s.add(Implies(cond, start[0] >= travel_time))

# 5. For consecutive positions, start[i+1] >= end[i] + travel_time between locations
for i in range(max_positions - 1):
    for fid_i in range(num_friends):
        for fid_j in range(num_friends):
            cond = And(seq[i] == fid_i, seq[i + 1] == fid_j)
            loc_i = friends[fid_i]['location']
            loc_j = friends[fid_j]['location']
            if (loc_i, loc_j) in travel_times:
                travel_time = travel_times[(loc_i, loc_j)]
            else:
                travel_time = 0  # Default if not found (should not happen)
            s.add(Implies(cond, start[i + 1] >= end[i] + travel_time))

# 6. Maximize the number of friends in the sequence
count = Sum([If(seq[i] > 0, 1, 0) for i in range(max_positions)])
s.maximize(count)

# Check for solution
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(max_positions):
        fid = m[seq[i]].as_long()
        if fid == 0:
            continue
        name = friends[fid]['name']
        st = m[start[i]].as_long()
        et = m[end[i]].as_long()
        start_time = f"{(st // 60):02d}:{(st % 60):02d}"
        end_time = f"{(et // 60):02d}:{(et % 60):02d}"
        itinerary.append({"action": "meet", "person": name, "start_time": start_time, "end_time": end_time})
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found")