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
meetings = [Bool(f'meeting_{i}') for i in range(2)]

# Define the constraints
s = Optimize()
for i in range(1, 13):
    s.add(times[i] >= times[i-1])
s.add(times[12] <= end_time)
s.add(Or(meetings[0], meetings[1]))
s.add(And(meetings[0] == Not(meetings[1])))

# Define the constraints for meeting times
for i in range(2):
    s.add(If(meetings[i], And(times[12] >= friends[list(friends.keys())[i]]['start'], times[12] <= friends[list(friends.keys())[i]]['end']), True))

# Define the constraints for travel times
for i in range(1, 13):
    for j in range(i+1, 13):
        if locations[i % 3]!= locations[j % 3]:
            s.add(If(Or(meetings[0], meetings[1]), And(times[j] >= times[i] + travel_distances[(locations[i % 3], locations[j % 3])]), True))

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
    for i in range(2):
        if model[meetings[i]].as_bool():
            friend = list(friends.keys())[i]
            print(f"Meeting {friend} from 9:00 AM to 10:30 AM")
else:
    print("No solution found")