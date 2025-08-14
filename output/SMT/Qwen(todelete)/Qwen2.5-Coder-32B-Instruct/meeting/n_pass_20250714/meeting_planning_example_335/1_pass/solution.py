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

# Define variables for each friend's meeting start time
meeting_start = {friend: Int(f'meeting_start_{friend}') for friend in friends_availability}

# Add constraints for each friend's availability
for friend, availability in friends_availability.items():
    solver.add(meeting_start[friend] >= availability['start'])
    solver.add(meeting_start[friend] + availability['min_duration'] <= availability['end'])

# Define variables for location changes
location_change_time = {i: Int(f'location_change_time_{i}') for i in range(len(locations) - 1)}

# Initial location is Pacific Heights at 9:00 AM
initial_location_time = 9 * 60

# Add constraints for location changes
current_location = 'Pacific Heights'
current_time = initial_location_time
for i in range(len(locations) - 1):
    next_location = locations[i + 1]
    travel_time = travel_times[(current_location, next_location)]
    solver.add(location_change_time[i] == current_time + travel_time)
    current_time = location_change_time[i]
    current_location = next_location

# Ensure that meetings happen after location changes
for friend, availability in friends_availability.items():
    if friend == 'Helen':
        solver.add(location_change_time[0] <= meeting_start[friend])
    elif friend == 'Kevin':
        solver.add(location_change_time[1] <= meeting_start[friend])
    elif friend == 'Amanda':
        solver.add(location_change_time[2] <= meeting_start[friend])
    elif friend == 'Betty':
        solver.add(location_change_time[3] <= meeting_start[friend])

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for friend, availability in friends_availability.items():
        start_time = model[meeting_start[friend]].as_long()
        end_time = start_time + availability['min_duration']
        print(f"Meet {friend} from {start_time//60}:{start_time%60:02d} to {end_time//60}:{end_time%60:02d}")
else:
    print("No solution found.")