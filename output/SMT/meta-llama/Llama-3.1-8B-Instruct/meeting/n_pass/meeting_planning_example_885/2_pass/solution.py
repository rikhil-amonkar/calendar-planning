from z3 import *

# Define the locations
locations = ['Russian Hill', 'Marina District', 'Financial District', 'Alamo Square', 
             'Golden Gate Park', 'The Castro', 'Bayview', 'Sunset District', 'Haight-Ashbury', 'Nob Hill']

# Define the travel times
travel_times = {
    'Russian Hill': {'Marina District': 7, 'Financial District': 11, 'Alamo Square': 15, 
                     'Golden Gate Park': 21, 'The Castro': 21, 'Bayview': 23, 'Sunset District': 23, 
                     'Haight-Ashbury': 17, 'Nob Hill': 5},
    'Marina District': {'Russian Hill': 8, 'Financial District': 17, 'Alamo Square': 15, 
                        'Golden Gate Park': 18, 'The Castro': 22, 'Bayview': 27, 'Sunset District': 19, 
                        'Haight-Ashbury': 16, 'Nob Hill': 12},
    'Financial District': {'Russian Hill': 11, 'Marina District': 15, 'Alamo Square': 17, 
                           'Golden Gate Park': 23, 'The Castro': 20, 'Bayview': 19, 'Sunset District': 30, 
                           'Haight-Ashbury': 19, 'Nob Hill': 8},
    'Alamo Square': {'Russian Hill': 13, 'Marina District': 15, 'Financial District': 17, 
                     'Golden Gate Park': 9, 'The Castro': 8, 'Bayview': 16, 'Sunset District': 16, 
                     'Haight-Ashbury': 5, 'Nob Hill': 11},
    'Golden Gate Park': {'Russian Hill': 19, 'Marina District': 16, 'Financial District': 26, 
                         'Alamo Square': 9, 'The Castro': 13, 'Bayview': 23, 'Sunset District': 10, 
                         'Haight-Ashbury': 7, 'Nob Hill': 20},
    'The Castro': {'Russian Hill': 18, 'Marina District': 21, 'Financial District': 21, 
                   'Alamo Square': 8, 'Golden Gate Park': 11, 'Bayview': 19, 'Sunset District': 17, 
                   'Haight-Ashbury': 6, 'Nob Hill': 16},
    'Bayview': {'Russian Hill': 23, 'Marina District': 27, 'Financial District': 19, 
                'Alamo Square': 16, 'Golden Gate Park': 22, 'The Castro': 19, 'Sunset District': 23, 
                'Haight-Ashbury': 19, 'Nob Hill': 20},
    'Sunset District': {'Russian Hill': 24, 'Marina District': 21, 'Financial District': 30, 
                        'Alamo Square': 17, 'Golden Gate Park': 11, 'The Castro': 17, 'Bayview': 22, 
                        'Haight-Ashbury': 15, 'Nob Hill': 27},
    'Haight-Ashbury': {'Russian Hill': 17, 'Marina District': 17, 'Financial District': 21, 
                       'Alamo Square': 5, 'Golden Gate Park': 7, 'The Castro': 6, 'Bayview': 18, 
                       'Sunset District': 15, 'Nob Hill': 15},
    'Nob Hill': {'Russian Hill': 5, 'Marina District': 11, 'Financial District': 9, 
                 'Alamo Square': 11, 'Golden Gate Park': 17, 'The Castro': 17, 'Bayview': 19, 
                 'Sunset District': 24, 'Haight-Ashbury': 13}
}

# Define the constraints
constraints = []
friends = {
    'Mark': {'location': 'Marina District','start_time': 6*60+45, 'end_time': 9*60,'min_time': 90*60},
    'Karen': {'location': 'Financial District','start_time': 9*60, 'end_time': 12*60+45,'min_time': 90*60},
    'Barbara': {'location': 'Alamo Square','start_time': 10*60, 'end_time': 19*60+30,'min_time': 90*60},
    'Nancy': {'location': 'Golden Gate Park','start_time': 16*60+45, 'end_time': 20*60,'min_time': 105*60},
    'David': {'location': 'The Castro','start_time': 9*60, 'end_time': 18*60,'min_time': 120*60},
    'Linda': {'location': 'Bayview','start_time': 18*60+15, 'end_time': 19*60+45,'min_time': 45*60},
    'Kevin': {'location': 'Sunset District','start_time': 10*60, 'end_time': 17*60+45,'min_time': 120*60},
    'Matthew': {'location': 'Haight-Ashbury','start_time': 10*60+15, 'end_time': 16*60+30,'min_time': 45*60},
    'Andrew': {'location': 'Nob Hill','start_time': 11*60+45, 'end_time': 17*60+45,'min_time': 105*60}
}

# Create variables for the arrival times
arrival_times = {}
for friend in friends:
    arrival_times[friend] = Int(f'arrival_time_{friend}')

# Create constraints for the arrival times
for friend in friends:
    location = friends[friend]['location']
    start_time = friends[friend]['start_time']
    end_time = friends[friend]['end_time']
    min_time = friends[friend]['min_time']

    constraints.append(arrival_times[friend] >= start_time)
    constraints.append(arrival_times[friend] <= end_time)
    constraints.append(arrival_times[friend] + min_time <= end_time)
    constraints.append(arrival_times[friend] + min_time >= start_time)

# Create a variable for the number of friends met
num_friends_met = Int('num_friends_met')
constraints.append(num_friends_met == 7)

# Create a solver
solver = Solver()
for constraint in constraints:
    solver.add(constraint)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    arrival_times_dict = {}
    for friend in friends:
        arrival_times_dict[friend] = model[getattr(model, f'arrival_time_{friend}')].as_long()

    # Calculate the total travel time
    total_travel_time = 0
    for i in range(len(locations) - 1):
        current_location = locations[i]
        next_location = locations[i + 1]
        travel_time = travel_times[current_location][next_location]
        total_travel_time += travel_time

    # Print the solution
    print('SOLUTION:')
    print(f'Arrival times: {arrival_times_dict}')
    print(f'Total travel time: {total_travel_time} minutes')
else:
    print('No solution found')