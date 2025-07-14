from z3 import *

# Define the locations
locations = ['Pacific Heights', 'North Beach', 'Financial District', 'Alamo Square', 'Mission District']

# Define the travel times in minutes
travel_times = {
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Mission District'): 15,
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Mission District'): 18,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Mission District'): 17,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Mission District'): 10,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Financial District'): 17,
    ('Mission District', 'Alamo Square'): 11
}

# Define the friends' availability and meeting durations
friends_availability = {
    'Helen': {'start': 9*60, 'end': 17*60, 'min_duration': 15},
    'Betty': {'start': 19*60, 'end': 21*45, 'min_duration': 90},
    'Amanda': {'start': 19*45, 'end': 21*60, 'min_duration': 60},
    'Kevin': {'start': 10*45, 'end': 14*45, 'min_duration': 45}
}

# Create a solver instance
solver = Solver()

# Define boolean variables to indicate whether to meet each friend
meet_helen = Bool('meet_helen')
meet_betty = Bool('meet_betty')
meet_amanda = Bool('meet_amanda')
meet_kevin = Bool('meet_kevin')

# Define variables for each friend's meeting start time
meeting_start = {
    'Helen': Int('meeting_start_Helen'),
    'Betty': Int('meeting_start_Betty'),
    'Amanda': Int('meeting_start_Amanda'),
    'Kevin': Int('meeting_start_Kevin')
}

# Add constraints for each friend's availability
for friend, availability in friends_availability.items():
    solver.add(Implies(meet_helen, meeting_start['Helen'] >= availability['start']))
    solver.add(Implies(meet_helen, meeting_start['Helen'] + availability['min_duration'] <= availability['end']))
    solver.add(Implies(meet_betty, meeting_start['Betty'] >= availability['start']))
    solver.add(Implies(meet_betty, meeting_start['Betty'] + availability['min_duration'] <= availability['end']))
    solver.add(Implies(meet_amanda, meeting_start['Amanda'] >= availability['start']))
    solver.add(Implies(meet_amanda, meeting_start['Amanda'] + availability['min_duration'] <= availability['end']))
    solver.add(Implies(meet_kevin, meeting_start['Kevin'] >= availability['start']))
    solver.add(Implies(meet_kevin, meeting_start['Kevin'] + availability['min_duration'] <= availability['end']))

# Ensure that exactly 3 friends are met
solver.add(meet_helen + meet_betty + meet_amanda + meet_kevin == 3)

# Define variables for location changes
location_change_time = [Int(f'location_change_time_{i}') for i in range(4)]

# Initial location is Pacific Heights at 9:00 AM
initial_location_time = 9 * 60

# Define the order of visits
visits = [Bool(f'visit_{loc}') for loc in locations[1:]]

# Constraints for visiting each location
solver.add(visits[0] == meet_helen)
solver.add(visits[1] == meet_betty)
solver.add(visits[2] == meet_amanda)
solver.add(visits[3] == meet_kevin)

# Add constraints for location changes
current_location = 'Pacific Heights'
current_time = initial_location_time
for i in range(4):
    next_location = locations[i + 1]
    travel_time = travel_times[(current_location, next_location)]
    solver.add(Implies(visits[i], location_change_time[i] == current_time + travel_time))
    solver.add(Implies(visits[i], meeting_start[friends_availability.keys()[i]] >= location_change_time[i]))
    current_time = location_change_time[i]
    current_location = next_location

# Ensure that meetings happen after location changes
for i, friend in enumerate(friends_availability.keys()):
    solver.add(Implies(visits[i], meeting_start[friend] + friends_availability[friend]['min_duration'] <= location_change_time[i] + 1000))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for friend, availability in friends_availability.items():
        if model[meet_helen] and friend == 'Helen':
            start_time = model[meeting_start[friend]].as_long()
            end_time = start_time + availability['min_duration']
            print(f"Meet {friend} from {start_time//60}:{start_time%60:02d} to {end_time//60}:{end_time%60:02d}")
        elif model[meet_betty] and friend == 'Betty':
            start_time = model[meeting_start[friend]].as_long()
            end_time = start_time + availability['min_duration']
            print(f"Meet {friend} from {start_time//60}:{start_time%60:02d} to {end_time//60}:{end_time%60:02d}")
        elif model[meet_amanda] and friend == 'Amanda':
            start_time = model[meeting_start[friend]].as_long()
            end_time = start_time + availability['min_duration']
            print(f"Meet {friend} from {start_time//60}:{start_time%60:02d} to {end_time//60}:{end_time%60:02d}")
        elif model[meet_kevin] and friend == 'Kevin':
            start_time = model[meeting_start[friend]].as_long()
            end_time = start_time + availability['min_duration']
            print(f"Meet {friend} from {start_time//60}:{start_time%60:02d} to {end_time//60}:{end_time%60:02d}")
else:
    print("No solution found.")