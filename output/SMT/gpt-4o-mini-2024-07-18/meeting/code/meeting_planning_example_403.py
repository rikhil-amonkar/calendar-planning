from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'The Castro'): 19,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'The Castro'): 16,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'The Castro'): 21,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'The Castro'): 22,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Chinatown'): 20,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Andrew': (705, 75),     # 11:45 AM - 2:30 PM
    'Sarah': (975, 15),      # 4:15 PM - 6:45 PM
    'Nancy': (1050, 60),     # 5:30 PM - 7:15 PM
    'Rebecca': (585, 90),    # 9:45 AM - 9:30 PM
    'Robert': (510, 30),     # 8:30 AM - 2:15 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Andrew': 75,
    'Sarah': 15,
    'Nancy': 60,
    'Rebecca': 90,
    'Robert': 30,
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

# Travel time constraints from Union Square (arrival at 9:00 AM)
travel_times_to_friends = {
    'Andrew': travel_times[('Union Square', 'Golden Gate Park')],
    'Sarah': travel_times[('Union Square', 'Pacific Heights')],
    'Nancy': travel_times[('Union Square', 'Presidio')],
    'Rebecca': travel_times[('Union Square', 'Chinatown')],
    'Robert': travel_times[('Union Square', 'The Castro')],
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