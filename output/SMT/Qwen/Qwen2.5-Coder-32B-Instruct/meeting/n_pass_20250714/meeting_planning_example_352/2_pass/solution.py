from z3 import *

# Define the travel times in minutes
travel_times = {
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Marina District'): 18,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Marina District'): 11,
    ('Haight-Ashbury', 'Union Square'): 17,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Nob Hill'): 8,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Marina District'): 12,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Chinatown'): 16,
}

# Define the availability and required meeting durations
availabilities = {
    'Karen': ((9*60 + 15, 9*60 + 45), 30),
    'Joseph': ((12*60 + 30, 19*60 + 45), 90),
    'Sandra': ((7*60 + 15, 19*60 + 15), 75),
    'Nancy': ((11*60, 20*60 + 15), 105)
}

# Create a solver instance
solver = Solver()

# Define integer variables for the start times of meetings
start_times = {name: Int(name) for name in availabilities}

# Add constraints for each friend
for name, ((start, end), duration) in availabilities.items():
    solver.add(start_times[name] >= start)
    solver.add(start_times[name] + duration <= end)

# Define the current location and initial time
current_location = 'Union Square'
current_time = 9 * 60  # 9:00 AM in minutes

# Define binary variables to indicate whether we meet each person
meet_vars = {name: Bool(name) for name in availabilities}

# Ensure we meet exactly 4 people
solver.add(Sum([If(meet_vars[name], 1, 0) for name in availabilities]) == 4)

# Function to add travel constraints
def add_travel_constraints(current_location, next_location, start_time_var, prev_end_time):
    travel_time = travel_times[(current_location, next_location)]
    solver.add(Implies(meet_vars[next_location], start_time_var >= prev_end_time + travel_time))

# Try all permutations of meeting friends
from itertools import permutations

# Generate all permutations of the friends
friends = list(availabilities.keys())
for perm in permutations(friends):
    # Reset current time and location
    current_time = 9 * 60
    current_location = 'Union Square'
    
    # Add constraints for the current permutation
    for i, name in enumerate(perm):
        if i == 0:
            # First meeting after initial travel from Union Square
            add_travel_constraints(current_location, name, start_times[name], current_time)
        else:
            # Subsequent meetings after traveling from the previous location
            add_travel_constraints(perm[i-1], name, start_times[name], start_times[perm[i-1]] + availabilities[perm[i-1]][1])
        
        # Ensure we meet the person
        solver.add(meet_vars[name])
    
    # Check if the solution is feasible
    if solver.check() == sat:
        model = solver.model()
        solution = {name: model[start_times[name]].as_long() for name in availabilities if model[meet_vars[name]]}
        print("SOLUTION:")
        for name, start_time in sorted(solution.items(), key=lambda x: x[1]):
            start_hour = start_time // 60
            start_minute = start_time % 60
            print(f"Meet {name} at {start_hour:02}:{start_minute:02}")
        break
else:
    print("No solution found")