from z3 import *

# Define the locations
locations = ['Presidio', 'Golden Gate Park', 'Bayview', 'Chinatown', 'North Beach', 'Mission District']

# Define the travel times (in minutes)
travel_times = {
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Mission District'): 26,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Bayview', 'Presidio'): 31,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Chinatown'): 18,
    ('Bayview', 'North Beach'): 21,
    ('Bayview', 'Mission District'): 13,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Bayview'): 22,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Mission District'): 18,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Bayview'): 22,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Mission District'): 18,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'North Beach'): 17,
}

# Define the friends and their availability
friends = {
    'Jessica': {'location': 'Golden Gate Park', 'start': 16.75, 'end': 18.0, 'min_duration': 0.5},
    'Ashley': {'location': 'Bayview', 'start': 17.25, 'end': 20.0, 'min_duration': 1.75},
    'Ronald': {'location': 'Chinatown', 'start': 7.25, 'end': 14.75, 'min_duration': 1.5},
    'William': {'location': 'North Beach', 'start': 13.25, 'end': 20.25, 'min_duration': 0.25},
    'Daniel': {'location': 'Mission District', 'start': 7.0, 'end': 11.25, 'min_duration': 1.75},
}

# Create a solver instance
solver = Solver()

# Define variables
current_time = Real('current_time')
visited = {friend: Bool(f'visited_{friend}') for friend in friends}
arrival_times = {location: Real(f'arrival_{location}') for location in locations}

# Initial conditions
solver.add(arrival_times['Presidio'] == 9.0)

# Add constraints for each friend
for friend, details in friends.items():
    loc = details['location']
    start = details['start']
    end = details['end']
    min_duration = details['min_duration']
    
    # Constraint to visit the friend within their available time
    solver.add(Implies(visited[friend], arrival_times[loc] + min_duration <= end))
    solver.add(Implies(visited[friend], arrival_times[loc] >= start))
    
    # Constraint to ensure the time spent traveling is respected
    for prev_loc in locations:
        if prev_loc != loc:
            solver.add(Implies(visited[friend], arrival_times[loc] >= arrival_times[prev_loc] + travel_times[(prev_loc, loc)] / 60.0))

# Constraint to visit exactly 5 friends
solver.add(Sum([If(visited[friend], 1, 0) for friend in friends]) == 5)

# Check if the constraints can be satisfied
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    print(f"Start at Presidio at 9:00 AM")
    for friend, details in friends.items():
        if model.evaluate(visited[friend]):
            loc = details['location']
            start_time = model.evaluate(arrival_times[loc]).as_decimal(3)
            end_time = model.evaluate(arrival_times[loc] + details['min_duration']).as_decimal(3)
            print(f"Meet {friend} at {loc} from {start_time} to {end_time}")
else:
    print("No solution found")