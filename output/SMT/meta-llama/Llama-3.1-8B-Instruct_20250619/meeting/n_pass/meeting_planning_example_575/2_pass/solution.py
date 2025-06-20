from z3 import *

# Define the travel distances
distances = {
    'The Castro': {'Presidio': 20, 'Sunset District': 17, 'Haight-Ashbury': 6, 'Mission District': 7, 'Golden Gate Park': 11, 'Russian Hill': 18},
    'Presidio': {'The Castro': 21, 'Sunset District': 15, 'Haight-Ashbury': 15, 'Mission District': 26, 'Golden Gate Park': 12, 'Russian Hill': 14},
    'Sunset District': {'The Castro': 17, 'Presidio': 16, 'Haight-Ashbury': 15, 'Mission District': 24, 'Golden Gate Park': 11, 'Russian Hill': 24},
    'Haight-Ashbury': {'The Castro': 6, 'Presidio': 15, 'Sunset District': 15, 'Mission District': 11, 'Golden Gate Park': 7, 'Russian Hill': 17},
    'Mission District': {'The Castro': 7, 'Presidio': 25, 'Sunset District': 24, 'Haight-Ashbury': 12, 'Golden Gate Park': 17, 'Russian Hill': 15},
    'Golden Gate Park': {'The Castro': 13, 'Presidio': 11, 'Sunset District': 10, 'Haight-Ashbury': 7, 'Mission District': 17, 'Russian Hill': 19},
    'Russian Hill': {'The Castro': 18, 'Presidio': 14, 'Sunset District': 23, 'Haight-Ashbury': 17, 'Mission District': 16, 'Golden Gate Park': 21}
}

# Define the friends and their availability
friends = {
    'Rebecca': {'location': 'Presidio','start': 6*60, 'end': 8*60,'min_time': 60},
    'Linda': {'location': 'Sunset District','start': 3*60, 'end': 7*60,'min_time': 30},
    'Elizabeth': {'location': 'Haight-Ashbury','start': 5*60, 'end': 7*60,'min_time': 105},
    'William': {'location': 'Mission District','start': 1*60, 'end': 7*60,'min_time': 30},
    'Robert': {'location': 'Golden Gate Park','start': 2*60, 'end': 9*60,'min_time': 45},
    'Mark': {'location': 'Russian Hill','start': 0, 'end': 9*60,'min_time': 75}
}

# Define the solver
solver = Solver()

# Define the variables
locations = list(distances.keys())
times = [9*60]  # start time
variables = [Bool(f'meet_{location}') for location in locations]
times_list = [Int(f'time_{i}') for i in range(len(locations))]

# Add constraints
for location in locations:
    solver.add(Or([variables[i] for i, loc in enumerate(locations) if loc == location]))

# Add constraints for each friend
for friend, info in friends.items():
    location = info['location']
    start = info['start']
    end = info['end']
    min_time = info['min_time']
    for i in range(len(locations)):
        if locations[i] == location:
            solver.add(variables[i])
            solver.add(start <= times_list[i] + min_time)
            solver.add(times_list[i] + min_time <= end)

# Add constraint for total time
for i in range(len(locations)):
    solver.add(times_list[i] >= times[0])
    solver.add(times_list[i] <= 9*60 + 60)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    schedule = []
    for i, location in enumerate(locations):
        if model.evaluate(variables[i]).as_bool():
            schedule.append((location, model.evaluate(times_list[i]).as_long()))
    schedule.sort(key=lambda x: x[1])
    print('SOLUTION:')
    for location, time in schedule:
        print(f'Meet at {location} at {time//60}:{(time%60):02d}')
else:
    print('No solution found')