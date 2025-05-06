from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman's Wharf', 'Marina District'): 9,
    ('Fisherman's Wharf', 'Embarcadero'): 8,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Nob Hill'): 20,
    ('Bayview', 'Marina District'): 25,
    ('Bayview', 'Embarcadero'): 19,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Nob Hill', 'Fisherman\'s Wharf'): 11,
    ('Nob Hill', 'Bayview'): 19,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Embarcadero'): 14,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Marina District'): 12,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Thomas': (1020, 120),  # 3:30 PM - 6:30 PM
    'Stephanie': (1080, 30), # 6:30 PM - 9:45 PM
    'Laura': (525, 30),      # 8:45 AM - 4:15 PM
    'Betty': (1145, 45),     # 6:45 PM - 9:45 PM
    'Patricia': (930, 45),   # 5:30 PM - 10:00 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Thomas': 120,
    'Stephanie': 30,
    'Laura': 30,
    'Betty': 45,
    'Patricia': 45,
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting times based on friends' availability
for friend in meeting_times:
    start_time, _ = meeting_times[friend]
    solver.add(meeting_start[friend] >= start_time)  # Must start after their availability time
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])  # Calculate end time

# Travel time constraints from Fisherman's Wharf (arrival at 9:00 AM)
travel_times_to_friends = {
    'Thomas': travel_times[('Fisherman\'s Wharf', 'Bayview')],
    'Stephanie': travel_times[('Fisherman\'s Wharf', 'Golden Gate Park')],
    'Laura': travel_times[('Fisherman\'s Wharf', 'Nob Hill')],
    'Betty': travel_times[('Fisherman\'s Wharf', 'Marina District')],
    'Patricia': travel_times[('Fisherman\'s Wharf', 'Embarcadero')],
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
    for friend in meeting_times:
        start = model[meeting_start[friend]].as_long() 
        end = model[meeting_end[friend]].as_long()
        print(f"{friend}: Start at {start} minutes after midnight, End at {end} minutes after midnight")
else:
    print("SOLUTION: No valid meeting schedule found.")