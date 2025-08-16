from z3 import *
import json

# Define travel times between districts
travel_time = {
    # Russian Hill
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Presidio'): 14,
    # Sunset District
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Presidio'): 16,
    # Union Square
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Presidio'): 24,
    # Nob Hill
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Sunset District'): 24,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Presidio'): 17,
    # Marina District
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Presidio'): 10,
    # Richmond District
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Presidio'): 7,
    # Financial District
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Presidio'): 22,
    # Embarcadero
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Presidio'): 20,
    # The Castro
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Presidio'): 20,
    # Alamo Square
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Richmond District'): 11,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Presidio'): 17,
    # Presidio
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Alamo Square'): 19,
}

# Friends' data
friends_data = [
    {'name': 'William', 'location': 'Presidio', 'availability_start': 0, 'availability_end': 225, 'duration': 60},
    {'name': 'Kimberly', 'location': 'Alamo Square', 'availability_start': 0, 'availability_end': 330, 'duration': 105},
    {'name': 'David', 'location': 'Sunset District', 'availability_start': 15, 'availability_end': 780, 'duration': 15},
    {'name': 'Kenneth', 'location': 'Union Square', 'availability_start': 735, 'availability_end': 765, 'duration': 15},
    {'name': 'Patricia', 'location': 'Nob Hill', 'availability_start': 360, 'availability_end': 615, 'duration': 120},
    {'name': 'Mary', 'location': 'Marina District', 'availability_start': 165, 'availability_end': 465, 'duration': 45},
    {'name': 'Charles', 'location': 'Richmond District', 'availability_start': 495, 'availability_end': 720, 'duration': 15},
    {'name': 'Joshua', 'location': 'Financial District', 'availability_start': 330, 'availability_end': 495, 'duration': 90},
    {'name': 'Ronald', 'location': 'Embarcadero', 'availability_start': 555, 'availability_end': 645, 'duration': 30},
    {'name': 'George', 'location': 'The Castro', 'availability_start': 135, 'availability_end': 600, 'duration': 105},
]

friends_locations = [
    'Presidio',  # 0
    'Alamo Square',  # 1
    'Sunset District',  # 2
    'Union Square',  # 3
    'Nob Hill',  # 4
    'Marina District',  # 5
    'Richmond District',  # 6
    'Financial District',  # 7
    'Embarcadero',  # 8
    'The Castro',  # 9
]

# Precompute travel_time_between_friends matrix
travel_time_between_friends = [[0 for _ in range(10)] for _ in range(10)]
for i in range(10):
    for j in range(10):
        from_loc = friends_locations[i]
        to_loc = friends_locations[j]
        travel_time_between_friends[i][j] = travel_time[(from_loc, to_loc)]

# Precompute travel_time_from_russian_hill_to_friend
travel_time_from_russian_hill_to_friend = [travel_time[('Russian Hill', loc)] for loc in friends_locations]

# Z3 setup
max_positions = 10
friends = [Int(f'friend_{i}') for i in range(max_positions)]
starts = [Int(f'start_{i}') for i in range(max_positions)]
ends = [Int(f'end_{i}') for i in range(max_positions)]
solver = Optimize()

# Constraints for friend_i to be between 0 and 10
for f in friends:
    solver.add(And(f >= 0, f <= 10))

# Constraints for each friend to be assigned to at most one position
for friend_idx in range(10):
    count = Sum([If(f == friend_idx, 1, 0) for f in friends])
    solver.add(count <= 1)

# Add constraints for each position
for i in range(max_positions):
    current_friend = friends[i]
    current_start = starts[i]
    current_end = ends[i]
    is_assigned = current_friend != 10
    # Availability and duration
    availability_start = Int(f'as_{i}')
    availability_end = Int(f'ae_{i}')
    duration = Int(f'd_{i}')
    solver.add(Implies(is_assigned, availability_start == friends_data[current_friend]['availability_start']))
    solver.add(Implies(is_assigned, availability_end == friends_data[current_friend]['availability_end']))
    solver.add(Implies(is_assigned, duration == friends_data[current_friend]['duration']))
    # End time
    solver.add(Implies(is_assigned, current_end == current_start + duration))
    # Availability constraints
    solver.add(Implies(is_assigned, current_start >= availability_start))
    solver.add(Implies(is_assigned, current_start + duration <= availability_end))
    # Arrival time
    arrival_time = Int(f'arrival_{i}')
    if i == 0:
        # From Russian Hill to current friend
        solver.add(Implies(is_assigned, arrival_time == travel_time_from_russian_hill_to_friend[current_friend]))
    else:
        prev_friend = friends[i-1]
        # Ensure previous friend is assigned
        solver.add(Implies(is_assigned, prev_friend != 10))
        # Travel time between prev and current
        tt_expr = 0
        for pi in range(10):
            for ci in range(10):
                tt_expr = If(And(prev_friend == pi, current_friend == ci), travel_time_between_friends[pi][ci], tt_expr)
        # Arrival time is ends[i-1] + tt_expr
        solver.add(Implies(is_assigned, arrival_time == ends[i-1] + tt_expr))
    # Start time >= arrival time
    solver.add(Implies(is_assigned, current_start >= arrival_time))

# Objective: maximize the number of friends assigned
objective = Sum([If(f != 10, 1, 0) for f in friends])
solver.maximize(objective)

# Solve
result = solver.check()
if result == sat:
    model = solver.model()
    itinerary = []
    for i in range(max_positions):
        f = model.eval(friends[i])
        if f != 10:
            name = friends_data[f.as_long()]['name']
            start = model.eval(starts[i])
            end = model.eval(ends[i])
            # Convert to HH:MM
            def to_time(minutes):
                hours = (9 + (minutes.as_long() // 60)) % 24
                mins = minutes.as_long() % 60
                return f"{hours:02d}:{mins:02d}"
            start_time = to_time(start)
            end_time = to_time(end)
            itinerary.append({"action": "meet", "person": name, "start_time": start_time, "end_time": end_time})
    # Filter and sort
    itinerary = [entry for entry in itinerary if entry['person'] is not None]
    itinerary.sort(key=lambda x: x['start_time'])
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")