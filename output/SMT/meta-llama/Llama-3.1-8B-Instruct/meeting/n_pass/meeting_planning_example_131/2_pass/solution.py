from z3 import *

# Define the constraints
start_time = 0
end_time = 24 * 60  # 24 hours in minutes

# Define the friends and their availability
friends = {
    'Jason': (10 * 60, 4 * 60 + 15),  # 10:00AM to 4:15PM
    'Kenneth': (3 * 60 + 30, 4 * 60 + 45)  # 3:30PM to 4:45PM
}

# Define the minimum meeting time for each friend
min_meeting_time = {
    'Jason': 90,
    'Kenneth': 45
}

# Define the possible locations
locations = ['Pacific Heights', 'Presidio', 'Marina District']

# Define the variables
locations_at_time = {}
for location in locations:
    locations_at_time[location] = [Bool(f'{location}_at_{i}') for i in range(start_time, end_time + 1)]

# Define the constraints for each friend
for friend, availability in friends.items():
    start_time_friend, end_time_friend = availability
    # The friend must be met for at least the minimum meeting time
    for i in range(start_time_friend, end_time_friend + 1):
        for location in locations:
            for j in range(i - min_meeting_time[friend], i):
                if j >= start_time and j < end_time:
                    locations_at_time[location][i] = Or(locations_at_time[location][i], locations_at_time[location][j])

# Solve the problem
solver = Solver()
for location in locations:
    for i in range(start_time, end_time + 1):
        solver.add(locations_at_time[location][i])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    print('SOLUTION:')
    for location in locations:
        for i in range(start_time, end_time + 1):
            if model.evaluate(locations_at_time[location][i]):
                print(f'You are at {location} at {i // 60}:{i % 60:02d}')
else:
    print('No solution found')