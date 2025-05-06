from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Bayview', 'The Castro'): 20,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Fisherman\'s Wharf', 'The Castro'): 26,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Alamo Square'): 20,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Rebecca': (540, 90),        # 9:00 AM - 12:45 PM
    'Amanda': (1110, 90),        # 6:30 PM - 9:45 PM
    'James': (585, 90),          # 9:45 AM - 9:15 PM
    'Sarah': (480, 90),          # 8:00 AM - 9:30 PM
    'Melissa': (540, 90),        # 9:00 AM - 6:45 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Rebecca': 90,
    'Amanda': 90,
    'James': 90,
    'Sarah': 90,
    'Melissa': 90,
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting times based on friends' availability
for friend in meeting_times.keys():
    start_time, _ = meeting_times[friend]
    solver.add(meeting_start[friend] >= start_time)  # Must start after their available time
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])  # Calculate end time

# Travel time constraints from The Castro (arrival at 9:00 AM)
travel_times_to_friends = {
    'Rebecca': travel_times[('The Castro', 'Bayview')],
    'Amanda': travel_times[('The Castro', 'Pacific Heights')],
    'James': travel_times[('The Castro', 'Alamo Square')],
    'Sarah': travel_times[('The Castro', 'Fisherman\'s Wharf')],
    'Melissa': travel_times[('The Castro', 'Golden Gate Park')],
}

# Add constraints for ensuring enough time to meet each friend after traveling
for friend, travel_time in travel_times_to_friends.items():
    solver.add(meeting_start[friend] >= 540 + travel_time)  # Must start after 9:00 AM + travel time (540 = 9:00 AM in minutes)

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
        print(f"{friend}: Start at {start} minutes after midnight, End at {end} minutes after midnight")
else:
    print("SOLUTION: No valid meeting schedule found.")