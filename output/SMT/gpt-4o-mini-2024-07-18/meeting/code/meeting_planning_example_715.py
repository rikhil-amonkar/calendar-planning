from z3 import *

# Define places
places = [
    'Presidio', 'Marina District', 'The Castro', 
    'Fisherman\'s Wharf', 'Bayview', 'Pacific Heights',
    'Mission District', 'Alamo Square', 'Golden Gate Park'
]

# Define travel times (in minutes)
travel_times = {
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Golden Gate Park'): 18,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Alamo Square'): 21,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Bayview', 'Presidio'): 32,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'The Castro'): 19,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Bayview'): 14,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Alamo Square'): 9,
}

# Define time frames for friends and durations (in minutes after 9:00 AM)
meeting_times = {
    'Amanda': (165, 450),      # 2:45 PM - 7:30 PM
    'Melissa': (30, 300),      # 9:30 AM - 5:00 PM
    'Jeffrey': (765, 405),      # 12:45 PM - 6:45 PM
    'Matthew': (615, 75),      # 10:15 AM - 1:15 PM
    'Nancy': (300, 570),       # 5:00 PM - 9:30 PM
    'Karen': (330, 510),       # 5:30 PM - 8:30 PM
    'Robert': (675, 330),      # 11:15 AM - 5:30 PM
    'Joseph': (510, 1170)      # 8:30 AM - 9:15 PM
}

# Minimum durations for each meeting
minimum_durations = {
    'Amanda': 105,
    'Melissa': 30,
    'Jeffrey': 120,
    'Matthew': 30,
    'Nancy': 105,
    'Karen': 105,
    'Robert': 120,
    'Joseph': 105
}

# Initialize Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting times based on friends' availability
for friend in meeting_times.keys():
    start_time, end_time = meeting_times[friend]
    solver.add(meeting_start[friend] >= start_time, meeting_start[friend] <= end_time)
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])

# Travel constraints from Presidio (where you arrive at 9:00 AM)
travel_times_to_friends = {
    'Amanda': travel_times[('Presidio', 'Marina District')],
    'Melissa': travel_times[('Presidio', 'The Castro')],
    'Jeffrey': travel_times[('Presidio', 'Fisherman\'s Wharf')],
    'Matthew': travel_times[('Presidio', 'Bayview')],
    'Nancy': travel_times[('Presidio', 'Pacific Heights')],
    'Karen': travel_times[('Presidio', 'Mission District')],
    'Robert': travel_times[('Presidio', 'Alamo Square')],
    'Joseph': travel_times[('Presidio', 'Golden Gate Park')]
}

# Add constraints for ensuring enough travel time to meet each friend
for friend, travel_time in travel_times_to_friends.items():
    solver.add(meeting_start[friend] >= travel_time)

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