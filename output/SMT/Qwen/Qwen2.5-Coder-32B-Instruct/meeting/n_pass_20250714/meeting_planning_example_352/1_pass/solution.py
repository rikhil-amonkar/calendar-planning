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

# Function to add travel constraints
def add_travel_constraints(current_location, next_location, start_time_var):
    global current_time
    travel_time = travel_times[(current_location, next_location)]
    solver.add(start_time_var >= current_time + travel_time)
    current_time = start_time_var + availabilities[next_location][1]

# Try to visit each friend in a sequence
# This is a simple greedy approach; Z3 will handle the optimization
for name in availabilities:
    if name == 'Karen':
        continue  # Karen is not available until 9:15 PM, which is too late
    add_travel_constraints(current_location, name, start_times[name])
    current_location = name

# Add Karen's meeting constraint separately since she is only available later
if current_location != 'Nob Hill':
    add_travel_constraints(current_location, 'Nob Hill', start_times['Karen'])

# Check if the solution is feasible
if solver.check() == sat:
    model = solver.model()
    solution = {name: model[start_times[name]].as_long() for name in availabilities}
    print("SOLUTION:")
    for name, start_time in sorted(solution.items(), key=lambda x: x[1]):
        start_hour = start_time // 60
        start_minute = start_time % 60
        print(f"Meet {name} at {start_hour:02}:{start_minute:02}")
else:
    print("No solution found")