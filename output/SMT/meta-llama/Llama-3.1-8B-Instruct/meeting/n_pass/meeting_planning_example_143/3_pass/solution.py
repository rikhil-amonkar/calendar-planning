from z3 import *

# Define the travel distances
travel_distances = {
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Embarcadero'): 6,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Embarcadero'): 10,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Pacific Heights'): 11
}

# Define the constraints
start_time = 0
end_time = 12 * 60  # 12 hours in minutes

# Define the friends and their meeting times
friends = {
    'Karen': {'start': 6 * 60 + 45, 'end': 8 * 60 + 15,'min_meeting': 90},
    'Mark': {'start': 1 * 60, 'end': 5 * 60 + 45,'min_meeting': 120}
}

# Define the variables
times = [Int(f'time_{i}') for i in range(13)]
locations = ['North Beach', 'Pacific Heights', 'Embarcadero']
locations_idx = {location: i for i, location in enumerate(locations)}

# Define the constraints
s = Optimize()
for i in range(1, 13):
    s.add(times[i] >= times[i-1])
s.add(times[12] <= end_time)

# Define the constraints for meeting friends
for friend, info in friends.items():
    s.add(And(times[12] >= info['start'], times[12] <= info['end']))
    s.add(times[12] >= info['min_meeting'])

# Define the constraints for travel times
for i in range(1, 13):
    for j in range(i+1, 13):
        if locations[i % 3]!= locations[j % 3]:
            s.add(And(times[j] >= times[i] + travel_distances[(locations[i % 3], locations[j % 3])]))

# Define the objective function
s.minimize(times[12])

# Solve the problem
solution = s.check()
if solution == sat:
    model = s.model()
    print("Best schedule:")
    for i in range(13):
        location = locations[model[times[i]].as_long() % 3]
        print(f"{i}:00 - {location}")
else:
    print("No solution found")