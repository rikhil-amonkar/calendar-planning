from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Mission District'): 26,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Bayview', 'Presidio'): 31,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Chinatown'): 18,
    ('Bayview', 'North Beach'): 21,
    ('Bayview', 'Mission District'): 13,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Bayview'): 22,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Mission District'): 18,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Bayview'): 22,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Mission District'): 18,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'North Beach'): 17,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Jessica': (1050, 30),  # 1:45 PM - 3:00 PM
    'Ashley': (1115, 105),   # 5:15 PM - 8:00 PM
    'Ronald': (435, 90),      # 7:15 AM - 2:45 PM
    'William': (75, 15),      # 1:15 PM - 8:15 PM
    'Daniel': (435, 105),     # 7:00 AM - 11:15 AM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Jessica': 30,
    'Ashley': 105,
    'Ronald': 90,
    'William': 15,
    'Daniel': 105,
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting times based on friends' availability
for friend in meeting_times.keys():
    start_time, _ = meeting_times[friend]
    solver.add(meeting_start[friend] >= start_time)  # Must be after their start time
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])  # Calculate end time

# Travel time constraints from Presidio (arrival at 9:00 AM)
travel_times_to_friends = {
    'Jessica': travel_times[('Presidio', 'Golden Gate Park')],
    'Ashley': travel_times[('Presidio', 'Bayview')],
    'Ronald': travel_times[('Presidio', 'Chinatown')],
    'William': travel_times[('Presidio', 'North Beach')],
    'Daniel': travel_times[('Presidio', 'Mission District')],
}

# Add constraints for ensuring enough time to meet each friend after traveling
for friend, travel_time in travel_times_to_friends.items():
    # When starting a meeting, we need to consider travel time, and it must be after 9 AM
    solver.add(meeting_start[friend] >= 540 + travel_time)  # 540 = 9:00 AM in minutes

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