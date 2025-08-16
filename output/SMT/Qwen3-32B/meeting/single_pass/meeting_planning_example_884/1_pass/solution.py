import z3

# Define friends and their data
friends_data = {
    'Robert': {
        'location': 'Chinatown',
        'available_start': 7 * 60 + 45,  # 7:45 AM
        'available_end': 17 * 60 + 30,    # 5:30 PM
        'duration': 120,
    },
    'David': {
        'location': 'Sunset District',
        'available_start': 12 * 60 + 30,  # 12:30 PM
        'available_end': 19 * 60 + 45,    # 7:45 PM
        'duration': 45,
    },
    'Matthew': {
        'location': 'Alamo Square',
        'available_start': 8 * 60 + 45,   # 8:45 AM
        'available_end': 13 * 60 + 45,    # 1:45 PM
        'duration': 90,
    },
    'Jessica': {
        'location': 'Financial District',
        'available_start': 9 * 60 + 30,   # 9:30 AM
        'available_end': 18 * 60 + 45,    # 6:45 PM
        'duration': 45,
    },
    'Melissa': {
        'location': 'North Beach',
        'available_start': 7 * 60 + 15,   # 7:15 AM
        'available_end': 16 * 60 + 45,    # 4:45 PM
        'duration': 45,
    },
    'Mark': {
        'location': 'Embarcadero',
        'available_start': 15 * 60 + 15,  # 3:15 PM
        'available_end': 17 * 60 + 0,     # 5:00 PM
        'duration': 45,
    },
    'Deborah': {
        'location': 'Presidio',
        'available_start': 19 * 60 + 0,   # 7:00 PM
        'available_end': 19 * 60 + 45,    # 7:45 PM
        'duration': 45,
    },
    'Karen': {
        'location': 'Golden Gate Park',
        'available_start': 19 * 60 + 30,  # 7:30 PM
        'available_end': 22 * 60 + 0,     # 10:00 PM
        'duration': 120,
    },
    'Laura': {
        'location': 'Bayview',
        'available_start': 21 * 60 + 15,  # 9:15 PM
        'available_end': 22 * 60 + 15,    # 10:15 PM
        'duration': 15,
    },
}

# Define travel times between locations
locations = ['Richmond District', 'Chinatown', 'Sunset District', 'Alamo Square', 'Financial District', 'North Beach', 'Embarcadero', 'Presidio', 'Golden Gate Park', 'Bayview']

travel_time = {
    'Richmond District': {
        'Chinatown': 20,
        'Sunset District': 11,
        'Alamo Square': 13,
        'Financial District': 22,
        'North Beach': 17,
        'Embarcadero': 19,
        'Presidio': 7,
        'Golden Gate Park': 9,
        'Bayview': 27,
    },
    'Chinatown': {
        'Richmond District': 20,
        'Sunset District': 29,
        'Alamo Square': 17,
        'Financial District': 5,
        'North Beach': 3,
        'Embarcadero': 5,
        'Presidio': 19,
        'Golden Gate Park': 23,
        'Bayview': 20,
    },
    'Sunset District': {
        'Richmond District': 12,
        'Chinatown': 30,
        'Alamo Square': 17,
        'Financial District': 30,
        'North Beach': 28,
        'Embarcadero': 30,
        'Presidio': 16,
        'Golden Gate Park': 11,
        'Bayview': 22,
    },
    'Alamo Square': {
        'Richmond District': 11,
        'Chinatown': 15,
        'Sunset District': 16,
        'Financial District': 17,
        'North Beach': 15,
        'Embarcadero': 16,
        'Presidio': 17,
        'Golden Gate Park': 9,
        'Bayview': 16,
    },
    'Financial District': {
        'Richmond District': 21,
        'Chinatown': 5,
        'Sunset District': 30,
        'Alamo Square': 17,
        'North Beach': 7,
        'Embarcadero': 4,
        'Presidio': 22,
        'Golden Gate Park': 23,
        'Bayview': 19,
    },
    'North Beach': {
        'Richmond District': 18,
        'Chinatown': 6,
        'Sunset District': 27,
        'Alamo Square': 16,
        'Financial District': 8,
        'Embarcadero': 6,
        'Presidio': 17,
        'Golden Gate Park': 22,
        'Bayview': 25,
    },
    'Embarcadero': {
        'Richmond District': 21,
        'Chinatown': 7,
        'Sunset District': 30,
        'Alamo Square': 19,
        'Financial District': 5,
        'North Beach': 5,
        'Presidio': 20,
        'Golden Gate Park': 25,
        'Bayview': 21,
    },
    'Presidio': {
        'Richmond District': 7,
        'Chinatown': 21,
        'Sunset District': 15,
        'Alamo Square': 19,
        'Financial District': 23,
        'North Beach': 18,
        'Embarcadero': 20,
        'Golden Gate Park': 12,
        'Bayview': 31,
    },
    'Golden Gate Park': {
        'Richmond District': 7,
        'Chinatown': 23,
        'Sunset District': 10,
        'Alamo Square': 9,
        'Financial District': 26,
        'North Beach': 23,
        'Embarcadero': 25,
        'Presidio': 11,
        'Bayview': 23,
    },
    'Bayview': {
        'Richmond District': 25,
        'Chinatown': 19,
        'Sunset District': 23,
        'Alamo Square': 16,
        'Financial District': 19,
        'North Beach': 22,
        'Embarcadero': 19,
        'Presidio': 32,
        'Golden Gate Park': 23,
    },
}

friends = list(friends_data.keys())

# Create Z3 variables
include = {name: z3.Bool(name + '_include') for name in friends}
start = {name: z3.Int(name + '_start') for name in friends}
end = {name: z3.Int(name + '_end') for name in friends}

solver = z3.Solver()

# Add constraints for each friend
for name in friends:
    loc = friends_data[name]['location']
    travel_time_from_richmond = travel_time['Richmond District'][loc]
    available_start = friends_data[name]['available_start']
    available_end = friends_data[name]['available_end']
    duration = friends_data[name]['duration']
    
    # If include[name] is True, then:
    solver.add(z3.Implies(include[name], start[name] >= available_start))
    solver.add(z3.Implies(include[name], end[name] <= available_end))
    solver.add(z3.Implies(include[name], end[name] == start[name] + duration))
    solver.add(z3.Implies(include[name], start[name] >= 540 + travel_time_from_richmond))

# Add constraints for each pair of friends
for i in range(len(friends)):
    for j in range(len(friends)):
        if i == j:
            continue
        A = friends[i]
        B = friends[j]
        loc_A = friends_data[A]['location']
        loc_B = friends_data[B]['location']
        time_AB = travel_time[loc_A][loc_B]
        time_BA = travel_time[loc_B][loc_A]
        # If both A and B are included, then either:
        # start_B >= end_A + time_AB
        # or
        # start_A >= end_B + time_BA
        solver.add(z3.Implies(z3.And(include[A], include[B]), 
            z3.Or(
                start[B] >= end[A] + time_AB,
                start[A] >= end[B] + time_BA
            )
        ))

# Now, find the maximum number of friends that can be included
max_friends = 0
best_model = None

# Try from 9 down to 1
for k in range(9, 0, -1):
    # Create a new solver with the original constraints
    new_solver = z3.Solver()
    for c in solver.assertions():
        new_solver.add(c)
    # Add the constraint that exactly k friends are included
    sum_include = sum(z3.If(include[name], 1, 0) for name in friends)
    new_solver.add(sum_include == k)
    if str(new_solver.check()) == 'sat':
        max_friends = k
        best_model = new_solver.model()
        break

# If no solution found, return empty
if best_model is None:
    print("No solution found")
else:
    # Extract the included friends
    included = [name for name in friends if best_model.eval(include[name])]
    # Sort by start time
    included_sorted = sorted(included, key=lambda name: best_model.eval(start[name]).as_long())
    # Build the itinerary
    itinerary = []
    for name in included_sorted:
        start_time = best_model.eval(start[name]).as_long()
        end_time = best_model.eval(end[name]).as_long()
        # Convert to HH:MM format
        def to_time(m):
            h = m // 60
            m = m % 60
            return f"{h:02d}:{m:02d}"
        start_str = to_time(start_time)
        end_str = to_time(end_time)
        itinerary.append({"action": "meet", "person": name, "start_time": start_str, "end_time": end_str})
    
    # Output the JSON
    import json
    print(json.dumps({"itinerary": itinerary}, indent=2))