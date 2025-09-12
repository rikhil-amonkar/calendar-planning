import z3
import json

# Define friends and their data
friends = [
    {
        'name': 'Elizabeth',
        'location': 'Marina District',
        'available_start': 19 * 60,  # 7:00 PM
        'available_end': 20 * 60 + 45,  # 8:45 PM
        'required_duration': 105
    },
    {
        'name': 'Joshua',
        'location': 'Presidio',
        'available_start': 8 * 60 + 30,  # 8:30 AM
        'available_end': 13 * 60 + 15,  # 1:15 PM
        'required_duration': 105
    },
    {
        'name': 'Timothy',
        'location': 'North Beach',
        'available_start': 19 * 60 + 45,  # 7:45 PM
        'available_end': 22 * 60,  # 10:00 PM
        'required_duration': 90
    },
    {
        'name': 'David',
        'location': 'Embarcadero',
        'available_start': 10 * 60 + 45,  # 10:45 AM
        'available_end': 12 * 60 + 30,  # 12:30 PM
        'required_duration': 30
    },
    {
        'name': 'Kimberly',
        'location': 'Haight-Ashbury',
        'available_start': 16 * 60 + 45,  # 4:45 PM
        'available_end': 21 * 60 + 30,  # 9:30 PM
        'required_duration': 75
    },
    {
        'name': 'Lisa',
        'location': 'Golden Gate Park',
        'available_start': 17 * 60 + 30,  # 5:30 PM
        'available_end': 21 * 60 + 45,  # 9:45 PM
        'required_duration': 45
    },
    {
        'name': 'Ronald',
        'location': 'Richmond District',
        'available_start': 8 * 60,  # 8:00 AM
        'available_end': 9 * 60 + 30,  # 9:30 AM
        'required_duration': 90
    },
    {
        'name': 'Stephanie',
        'location': 'Alamo Square',
        'available_start': 15 * 60 + 30,  # 3:30 PM
        'available_end': 16 * 60 + 30,  # 4:30 PM
        'required_duration': 30
    },
    {
        'name': 'Helen',
        'location': 'Financial District',
        'available_start': 17 * 60 + 30,  # 5:30 PM
        'available_end': 18 * 60 + 30,  # 6:30 PM
        'required_duration': 45
    },
    {
        'name': 'Laura',
        'location': 'Sunset District',
        'available_start': 17 * 60 + 45,  # 5:45 PM
        'available_end': 21 * 60 + 15,  # 9:15 PM
        'required_duration': 90
    }
]

# Define travel times between locations
travel_times = {
    'Castro': {
        'Marina District': 21,
        'Presidio': 20,
        'North Beach': 20,
        'Embarcadero': 22,
        'Haight-Ashbury': 6,
        'Golden Gate Park': 11,
        'Richmond District': 16,
        'Alamo Square': 8,
        'Financial District': 21,
        'Sunset District': 17,
    },
    'Marina District': {
        'Castro': 22,
        'Presidio': 10,
        'North Beach': 11,
        'Embarcadero': 14,
        'Haight-Ashbury': 16,
        'Golden Gate Park': 18,
        'Richmond District': 11,
        'Alamo Square': 15,
        'Financial District': 17,
        'Sunset District': 19,
    },
    'Presidio': {
        'Castro': 21,
        'Marina District': 11,
        'North Beach': 18,
        'Embarcadero': 20,
        'Haight-Ashbury': 15,
        'Golden Gate Park': 12,
        'Richmond District': 7,
        'Alamo Square': 19,
        'Financial District': 23,
        'Sunset District': 15,
    },
    'North Beach': {
        'Castro': 23,
        'Marina District': 9,
        'Presidio': 17,
        'Embarcadero': 6,
        'Haight-Ashbury': 18,
        'Golden Gate Park': 22,
        'Richmond District': 18,
        'Alamo Square': 16,
        'Financial District': 8,
        'Sunset District': 27,
    },
    'Embarcadero': {
        'Castro': 25,
        'Marina District': 12,
        'Presidio': 20,
        'North Beach': 5,
        'Haight-Ashbury': 21,
        'Golden Gate Park': 25,
        'Richmond District': 21,
        'Alamo Square': 19,
        'Financial District': 5,
        'Sunset District': 30,
    },
    'Haight-Ashbury': {
        'Castro': 6,
        'Marina District': 17,
        'Presidio': 15,
        'North Beach': 19,
        'Embarcadero': 20,
        'Golden Gate Park': 7,
        'Richmond District': 10,
        'Alamo Square': 5,
        'Financial District': 21,
        'Sunset District': 15,
    },
    'Golden Gate Park': {
        'Castro': 13,
        'Marina District': 16,
        'Presidio': 11,
        'North Beach': 23,
        'Embarcadero': 25,
        'Haight-Ashbury': 7,
        'Richmond District': 7,
        'Alamo Square': 9,
        'Financial District': 26,
        'Sunset District': 10,
    },
    'Richmond District': {
        'Castro': 16,
        'Marina District': 9,
        'Presidio': 7,
        'North Beach': 17,
        'Embarcadero': 19,
        'Haight-Ashbury': 10,
        'Golden Gate Park': 9,
        'Alamo Square': 13,
        'Financial District': 22,
        'Sunset District': 11,
    },
    'Alamo Square': {
        'Castro': 8,
        'Marina District': 15,
        'Presidio': 17,
        'North Beach': 15,
        'Embarcadero': 16,
        'Haight-Ashbury': 5,
        'Golden Gate Park': 9,
        'Richmond District': 11,
        'Financial District': 17,
        'Sunset District': 16,
    },
    'Financial District': {
        'Castro': 20,
        'Marina District': 15,
        'Presidio': 22,
        'North Beach': 7,
        'Embarcadero': 4,
        'Haight-Ashbury': 19,
        'Golden Gate Park': 23,
        'Richmond District': 21,
        'Alamo Square': 17,
        'Sunset District': 30,
    },
    'Sunset District': {
        'Castro': 17,
        'Marina District': 21,
        'Presidio': 16,
        'North Beach': 28,
        'Embarcadero': 30,
        'Haight-Ashbury': 15,
        'Golden Gate Park': 11,
        'Richmond District': 12,
        'Alamo Square': 17,
        'Financial District': 30,
    },
}

# Precompute travel times between friends
friend_locations = [f['location'] for f in friends]
num_friends = len(friends)
travel_time_between = [[0]*num_friends for _ in range(num_friends)]
for j in range(num_friends):
    for k in range(num_friends):
        loc_j = friend_locations[j]
        loc_k = friend_locations[k]
        travel_time_between[j][k] = travel_times[loc_j][loc_k]

# Precompute travel time from Castro to each friend's location
travel_time_from_castro = [travel_times['Castro'][loc] for loc in friend_locations]

# Create Z3 solver
solver = z3.Solver()

# Create variables for each step (0 to 9)
friend = [z3.Int('friend_%d' % i) for i in range(10)]
start = [z3.Int('start_%d' % i) for i in range(10)]
end = [z3.Int('end_%d' % i) for i in range(10)]

# Add constraints for each friend's availability and duration
for i in range(10):
    # If friend_i is not -1, then start_i >= available_start, end_i = start_i + duration, end_i <= available_end
    f = friends[i]
    solver.add(z3.Implies(friend[i] != -1, start[i] >= f['available_start']))
    solver.add(z3.Implies(friend[i] != -1, end[i] == start[i] + f['required_duration']))
    solver.add(z3.Implies(friend[i] != -1, end[i] <= f['available_end']))

# Add constraint for first step's travel time
for i in range(10):
    solver.add(z3.Implies(friend[i] != -1, start[i] >= 540 + travel_time_from_castro[i]))

# Add constraints for consecutive steps' travel time
for i in range(1, 10):
    # For each step i, if friend[i] != -1 and friend[i-1] != -1, then start[i] >= end[i-1] + travel_time_between[friend[i-1]][friend[i]]
    for j in range(num_friends):
        for k in range(num_friends):
            solver.add(z3.Implies(
                z3.And(friend[i-1] == j, friend[i] == k),
                start[i] >= end[i-1] + travel_time_between[j][k]
            ))

# Add constraint to ensure valid steps are contiguous
for i in range(1, 10):
    for j in range(i):
        solver.add(z3.Implies(friend[i] != -1, friend[j] != -1))

# Add constraint to ensure no duplicate friends
for i in range(10):
    for j in range(i+1, 10):
        solver.add(z3.Implies(z3.And(friend[i] != -1, friend[j] != -1), friend[i] != friend[j]))

# Calculate total friends met
total_friends = z3.Sum([z3.If(friend[i] != -1, 1, 0) for i in range(10)])

# Try to find the maximum number of friends
max_k = 0
best_model = None
for k in range(10, 0, -1):
    solver.push()
    solver.add(total_friends >= k)
    if solver.check() == z3.sat:
        max_k = k
        best_model = solver.model()
        break
    else:
        solver.pop()

if best_model is None:
    print("No solution found")
else:
    # Extract the valid steps
    valid_steps = []
    for i in range(10):
        fi = best_model.eval(friend[i])
        if fi != -1:
            fi_int = fi.as_long()
            valid_steps.append({
                'step': i,
                'friend_index': fi_int,
                'start': best_model.eval(start[i]).as_long(),
                'end': best_model.eval(end[i]).as_long()
            })

    # Generate itinerary
    itinerary = []
    for step in valid_steps:
        f_index = step['friend_index']
        f = friends[f_index]
        start_time = step['start']
        end_time = step['end']
        # Convert to H:MM format
        def to_time_str(m):
            h = m // 60
            mm = m % 60
            return f"{h}:{mm:02d}"
        itinerary.append({
            "action": "meet",
            "location": f['location'],
            "person": f['name'],
            "start_time": to_time_str(start_time),
            "end_time": to_time_str(end_time)
        })

    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))