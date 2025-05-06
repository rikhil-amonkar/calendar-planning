from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Marina District'): 12,
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Chinatown'): 19,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Nob Hill'): 20,
    ('Bayview', 'Presidio'): 32,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'The Castro'): 19,
    ('Bayview', 'North Beach'): 22,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Marina District'): 27,
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'Bayview'): 20,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Chinatown', 'Marina District'): 12,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Chinatown'): 15,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Marina District'): 15,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Bayview'): 19,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Fisherman\'s Wharf'): 10,
    ('Nob Hill', 'Marina District'): 11,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Marina District'): 11,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Marina District'): 18,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Chinatown'): 22,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Marina District'): 21,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Bayview'): 25,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'The Castro'): 23,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Alamo Square'): 21,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Matthew': (1110, 120),    # 7:15 PM - 10:00 PM
    'Karen': (1110, 90),       # 7:15 PM - 9:15 PM
    'Sarah': (1170, 105),      # 8:00 PM - 9:45 PM
    'Jessica': (270, 120),     # 4:30 PM - 6:45 PM
    'Stephanie': (630, 60),    # 7:30 AM - 10:15 AM
    'Mary': (945, 60),         # 4:45 PM - 9:30 PM
    'Charles': (270, 105),     # 4:30 PM - 10:00 PM
    'Nancy': (165, 15),        # 2:45 PM - 8:00 PM
    'Thomas': (90, 30),        # 1:30 PM - 7:00 PM
    'Brian': (735, 60),        # 12:15 PM - 6:00 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Matthew': 120,
    'Karen': 90,
    'Sarah': 105,
    'Jessica': 120,
    'Stephanie': 60,
    'Mary': 60,
    'Charles': 105,
    'Nancy': 15,
    'Thomas': 30,
    'Brian': 60,
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting times based on friends' availability
for friend in meeting_times:
    start_time, _ = meeting_times[friend]
    solver.add(meeting_start[friend] >= start_time)  # Must start after their available time
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])  # Calculate end time

# Travel time constraints from Embarcadero (arrival at 9:00 AM)
travel_times_to_friends = {
    'Matthew': travel_times[('Embarcadero', 'Bayview')],
    'Karen': travel_times[('Embarcadero', 'Chinatown')],
    'Sarah': travel_times[('Embarcadero', 'Alamo Square')],
    'Jessica': travel_times[('Embarcadero', 'Nob Hill')],
    'Stephanie': travel_times[('Embarcadero', 'Presidio')],
    'Mary': travel_times[('Embarcadero', 'Union Square')],
    'Charles': travel_times[('Embarcadero', 'The Castro')],
    'Nancy': travel_times[('Embarcadero', 'North Beach')],
    'Thomas': travel_times[('Embarcadero', 'Fisherman\'s Wharf')],
    'Brian': travel_times[('Embarcadero', 'Marina District')],
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