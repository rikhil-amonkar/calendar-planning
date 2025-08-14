from z3 import *

# Define the locations
locations = ['Bayview', 'North Beach', 'Presidio', 'Haight-Ashbury', 'Union Square']

# Define the travel times in minutes
travel_times = {
    ('Bayview', 'North Beach'): 21,
    ('Bayview', 'Presidio'): 31,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Union Square'): 17,
    ('North Beach', 'Bayview'): 22,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Union Square'): 7,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Union Square'): 22,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Union Square'): 17,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Haight-Ashbury'): 18,
}

# Define the constraints for each friend
friend_constraints = {
    'Barbara': {'location': 'North Beach', 'start': 13.75, 'end': 20.25, 'duration': 1},
    'Margaret': {'location': 'Presidio', 'start': 10.25, 'end': 15.25, 'duration': 0.5},
    'Kevin': {'location': 'Haight-Ashbury', 'start': 20.0, 'end': 20.75, 'duration': 0.5},
    'Kimberly': {'location': 'Union Square', 'start': 7.75, 'end': 16.75, 'duration': 0.5},
}

# Create a solver instance
solver = Solver()

# Define the variables for the time spent at each location
time_spent = {loc: Real(f'time_spent_{loc}') for loc in locations}

# Define the variables for the arrival time at each location
arrival_time = {loc: Real(f'arrival_time_{loc}') for loc in locations}

# Set the initial arrival time at Bayview
solver.add(arrival_time['Bayview'] == 9.0)

# Add constraints for each location
for loc in locations:
    if loc != 'Bayview':
        # Arrival time at a location is the arrival time at the previous location plus travel time
        for prev_loc in locations:
            if prev_loc != loc:
                solver.add(Or(arrival_time[loc] >= arrival_time[prev_loc] + travel_times[(prev_loc, loc)] / 60,
                             arrival_time[prev_loc] >= arrival_time[loc] + travel_times[(loc, prev_loc)] / 60))

# Add constraints for meeting each friend
for friend, constraints in friend_constraints.items():
    loc = constraints['location']
    start = constraints['start']
    end = constraints['end']
    duration = constraints['duration']
    # Ensure we arrive at the location within the friend's availability and spend enough time there
    solver.add(arrival_time[loc] <= end - duration)
    solver.add(arrival_time[loc] + duration >= start)
    # Ensure we spend the required time meeting the friend
    solver.add(time_spent[loc] >= duration)

# Add constraints for time spent at each location
for loc in locations:
    solver.add(time_spent[loc] >= 0)

# Ensure we meet exactly 4 people
solver.add(Sum([If(time_spent[constraints['location']] > 0, 1, 0) for constraints in friend_constraints.values()]) == 4)

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for loc in locations:
        arr_time = model[arrival_time[loc]].as_decimal(2)
        spent_time = model[time_spent[loc]].as_decimal(2)
        print(f"Arrival time at {loc}: {arr_time} ({int(float(arr_time))}:{int((float(arr_time) % 1) * 60):02d})")
        print(f"Time spent at {loc}: {spent_time} hours")
else:
    print("No solution found")