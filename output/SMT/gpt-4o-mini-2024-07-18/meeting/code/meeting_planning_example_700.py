from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'North Beach'): 18,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'North Beach'): 9,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Alamo Square'): 21,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'North Beach'): 11,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'North Beach'): 15,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'North Beach'): 28,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Fisherman\'s Wharf'): 10,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Sunset District'): 24,
    ('Nob Hill', 'North Beach'): 8,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Nob Hill'): 7,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Kevin': (435, 90),        # 7:15 AM - 8:45 AM
    'Michelle': (1200, 15),    # 8:00 PM - 9:00 PM
    'Emily': (915, 30),        # 4:15 PM - 7:00 PM
    'Mark': (375, 75),         # 6:15 PM - 7:45 PM
    'Barbara': (900, 120),     # 5:00 PM - 7:00 PM
    'Laura': (840, 75),        # 7:00 PM - 9:15 PM
    'Mary': (750, 45),         # 5:30 PM - 7:00 PM
    'Helen': (660, 45),        # 11:00 AM - 12:15 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Kevin': 90,
    'Michelle': 15,
    'Emily': 30,
    'Mark': 75,
    'Barbara': 120,
    'Laura': 75,
    'Mary': 45,
    'Helen': 45,
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting times based on friends' availability
for friend in meeting_times.keys():
    start_time, _ = meeting_times[friend]
    solver.add(meeting_start[friend] >= start_time)  # Must be after the start time
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])  # Calculate end time

# Travel constraints from Presidio (arrival at 9:00 AM)
travel_times_to_friends = {
    'Kevin': travel_times[('Presidio', 'Pacific Heights')],
    'Michelle': travel_times[('Presidio', 'Golden Gate Park')],
    'Emily': travel_times[('Presidio', 'Fisherman\'s Wharf')],
    'Mark': travel_times[('Presidio', 'Marina District')],
    'Barbara': travel_times[('Presidio', 'Alamo Square')],
    'Laura': travel_times[('Presidio', 'Sunset District')],
    'Mary': travel_times[('Presidio', 'Nob Hill')],
    'Helen': travel_times[('Presidio', 'North Beach')],
}

# Add constraints for ensuring enough time to meet each friend
for friend, travel_time in travel_times_to_friends.items():
    solver.add(meeting_start[friend] >= travel_time)  # Must start after travel time

# Objective: maximize total meeting time
total_meeting_time = Sum([meeting_end[friend] - meeting_start[friend] for friend in meeting_times])
solver.maximize(total_meeting_time)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for friend in meeting_times.keys():
        start = model[meeting_start[friend]].as_long() 
        end = model[meeting_end[friend]].as_long()
        print(f"{friend}: Start at {start} minutes after 9:00 AM, End at {end} minutes after 9:00 AM")
else:
    print("SOLUTION: No valid meeting schedule found.")