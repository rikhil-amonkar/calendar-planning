from z3 import *

# Define the locations
locations = ['North Beach', 'Pacific Heights', 'Chinatown', 'Union Square', 
             'Mission District', 'Golden Gate Park', 'Nob Hill']

# Define the travel times (in minutes)
travel_times = {
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Mission District'): 18,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Nob Hill'): 7,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Mission District'): 18,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Nob Hill'): 8,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Nob Hill'): 9,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Nob Hill'): 12,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Golden Gate Park'): 17,
}

# Define the friends' availability and meeting requirements
friends = {
    'James': {'location': 'Pacific Heights', 'start': 20*60, 'end': 22*60, 'duration': 120},
    'Robert': {'location': 'Chinatown', 'start': 12*60 + 15, 'end': 16*60 + 45, 'duration': 90},
    'Jeffrey': {'location': 'Union Square', 'start': 9*60 + 30, 'end': 15*60 + 30, 'duration': 120},
    'Carol': {'location': 'Mission District', 'start': 18*60 + 15, 'end': 21*60 + 15, 'duration': 15},
    'Mark': {'location': 'Golden Gate Park', 'start': 11*60 + 30, 'end': 17*60 + 45, 'duration': 15},
    'Sandra': {'location': 'Nob Hill', 'start': 8*60, 'end': 15*60 + 30, 'duration': 15},
}

# Create a solver instance
solver = Solver()

# Define variables for the time spent at each location
time_at_location = {loc: Int(f'time_at_{loc}') for loc in locations}

# Define variables for the arrival time at each location
arrival_time = {loc: Int(f'arrival_time_{loc}') for loc in locations}

# Set initial arrival time at North Beach
solver.add(arrival_time['North Beach'] == 9*60)

# Add constraints for arrival times at other locations
for i in range(1, len(locations)):
    prev_loc = locations[i-1]
    curr_loc = locations[i]
    solver.add(arrival_time[curr_loc] == arrival_time[prev_loc] + travel_times[(prev_loc, curr_loc)] + time_at_location[prev_loc])

# Add constraints for meeting friends
meeting_constraints = []
for friend, details in friends.items():
    loc = details['location']
    start = details['start']
    end = details['end']
    duration = details['duration']
    
    # Ensure we arrive at the location before the friend leaves and leave after the friend arrives
    solver.add(arrival_time[loc] + duration <= end)
    solver.add(arrival_time[loc] >= start)
    # Ensure we spend the required duration with the friend
    solver.add(time_at_location[loc] >= duration)
    # Add a constraint to indicate if we meet the friend
    meeting_constraints.append(time_at_location[loc] >= duration)

# Add constraints for non-negative time spent at each location
for loc in locations:
    solver.add(time_at_location[loc] >= 0)

# Ensure we meet exactly 6 people
solver.add(Sum([If(constraint, 1, 0) for constraint in meeting_constraints]) == 6)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {loc: model[arrival_time[loc]].as_long() // 60 for loc in locations}
    print("SOLUTION:")
    for loc, time in solution.items():
        print(f"Arrive at {loc} at {time}:00")
else:
    print("No solution found")