from z3 import *

# Define the travel distances in minutes
travel_distances = {
    'Embarcadero': {'Golden Gate Park': 25, 'Haight-Ashbury': 21, 'Bayview': 21, 'Presidio': 20, 'Financial District': 5},
    'Golden Gate Park': {'Embarcadero': 25, 'Haight-Ashbury': 7, 'Bayview': 23, 'Presidio': 11, 'Financial District': 26},
    'Haight-Ashbury': {'Embarcadero': 20, 'Golden Gate Park': 7, 'Bayview': 18, 'Presidio': 15, 'Financial District': 21},
    'Bayview': {'Embarcadero': 19, 'Golden Gate Park': 22, 'Haight-Ashbury': 19, 'Presidio': 31, 'Financial District': 19},
    'Presidio': {'Embarcadero': 20, 'Golden Gate Park': 12, 'Haight-Ashbury': 15, 'Bayview': 31, 'Financial District': 23},
    'Financial District': {'Embarcadero': 4, 'Golden Gate Park': 23, 'Haight-Ashbury': 19, 'Bayview': 19, 'Presidio': 22}
}

# Define the constraints
constraints = [
    ('Mary', 8*60 + 45, 11*60 + 45),  # Mary is at Golden Gate Park from 8:45AM to 11:45AM
    ('Kevin', 10*60 + 15, 16*60 + 15),  # Kevin is at Haight-Ashbury from 10:15AM to 4:15PM
    ('Deborah', 15*60, 19*60 + 15),  # Deborah is at Bayview from 3:00PM to 7:15PM
    ('Stephanie', 10*60, 17*60 + 15),  # Stephanie is at Presidio from 10:00AM to 5:15PM
    ('Emily', 11*60 + 30, 21*60 + 45)  # Emily is at Financial District from 11:30AM to 9:45PM
]

# Define the solver
solver = Optimize()

# Define the variables
times = {}
for person, start, end in constraints:
    times[person] = [Bool(f'{person}_start'), Bool(f'{person}_end')]
    solver.add(times[person][0] == start / 60)
    solver.add(times[person][1] == end / 60)

# Define the constraints for meeting times
for person, start, end in constraints:
    solver.add(times[person][1] - times[person][0] >= 45 / 60)  # Meet for at least 45 minutes
    for other_person, other_start, other_end in constraints:
        if person!= other_person:
            solver.add(times[person][1] - times[person][0] >= abs(other_start - other_end) / 60)  # Meet for at least the duration of the other person's availability

# Define the constraints for travel times
for person, start, end in constraints:
    for location, distance in travel_distances['Embarcadero'].items():
        solver.add(times[person][0] >= start + distance)
    for location, distance in travel_distances[location].items():
        solver.add(times[person][1] <= end - distance)

# Solve the problem
result = solver.check()

# Print the result
if result == sat:
    model = solver.model()
    schedule = {}
    for person, start, end in constraints:
        schedule[person] = (model[times[person][0]].as_long() * 60, model[times[person][1]].as_long() * 60)
    print('SOLUTION:')
    for person, (start, end) in schedule.items():
        print(f'Meet {person} from {start} to {end} minutes')
else:
    print('No solution found')