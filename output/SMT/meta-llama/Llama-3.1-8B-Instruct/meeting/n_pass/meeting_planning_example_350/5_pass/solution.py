from z3 import *

# Define the variables
start_time = 0
end_time = 720  # 720 minutes in a day (12 hours * 60 minutes)
locations = ['Bayview', 'Pacific Heights', 'Mission District', 'Haight-Ashbury', 'Financial District']
friends = ['Mary', 'Lisa', 'Betty', 'Charles']
schedules = {location: [Bool(f'{location}_{friend}') for friend in friends] for location in locations}
travel_times = {
    'Bayview': {'Pacific Heights': 23, 'Mission District': 13, 'Haight-Ashbury': 19, 'Financial District': 19},
    'Pacific Heights': {'Bayview': 22, 'Mission District': 15, 'Haight-Ashbury': 11, 'Financial District': 13},
    'Mission District': {'Bayview': 15, 'Pacific Heights': 16, 'Haight-Ashbury': 12, 'Financial District': 17},
    'Haight-Ashbury': {'Bayview': 18, 'Pacific Heights': 12, 'Mission District': 11, 'Financial District': 21},
    'Financial District': {'Bayview': 19, 'Pacific Heights': 13, 'Mission District': 17, 'Haight-Ashbury': 19}
}

# Define the constraints
solver = Solver()

# Ensure exactly 4 people are met
num_people_met = [0] * 5
for location in locations:
    for friend in friends:
        if friend == 'Mary':
            start_time_mary = 600  # 10:00 AM
            end_time_mary = 420  # 7:00 PM
            availability_mary = [0] * 720
            availability_mary[start_time_mary:end_time_mary] = [1] * (end_time_mary - start_time_mary)
        elif friend == 'Lisa':
            start_time_lisa = 480  # 8:30 PM
            end_time_lisa = 600  # 10:00 PM
            availability_lisa = [0] * 720
            availability_lisa[start_time_lisa:end_time_lisa] = [1] * (end_time_lisa - start_time_lisa)
        elif friend == 'Betty':
            start_time_betty = 0  # 7:15 AM
            end_time_betty = 315  # 5:15 PM
            availability_betty = [0] * 720
            availability_betty[start_time_betty:end_time_betty] = [1] * (end_time_betty - start_time_betty)
        elif friend == 'Charles':
            start_time_charles = 675  # 11:15 AM
            end_time_charles = 180  # 3:00 PM
            availability_charles = [0] * 720
            availability_charles[start_time_charles:end_time_charles] = [1] * (end_time_charles - start_time_charles)

        # Ensure the friend is available at the location
        if friend == 'Mary':
            solver.add(schedules[location][friends.index(friend)] == True)
            solver.add(availability_mary[600 + friends.index(friend)] == 1)
        elif friend == 'Lisa':
            solver.add(schedules[location][friends.index(friend)] == True)
            solver.add(availability_lisa[480 + friends.index(friend)] == 1)
        elif friend == 'Betty':
            solver.add(schedules[location][friends.index(friend)] == True)
            solver.add(availability_betty[friends.index(friend)] == 1)
        elif friend == 'Charles':
            solver.add(schedules[location][friends.index(friend)] == True)
            solver.add(availability_charles[675 + friends.index(friend)] == 1)

        # Ensure exactly 4 people are met at the location
        num_people_met[locations.index(location)] += 1
        solver.add(num_people_met[locations.index(location)] == 1)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for location in locations:
        for i, friend in enumerate(friends):
            if model.evaluate(schedules[location][i]).as_bool():
                print(f"Meet {friend} at {location} for 45 minutes.")
else:
    print("No solution found.")