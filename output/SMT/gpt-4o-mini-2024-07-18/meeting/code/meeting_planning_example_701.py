from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'Richmond District'): 20,
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Chinatown'): 22,
    ('The Castro', 'Richmond District'): 16,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Richmond District'): 14,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Richmond District'): 7,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Richmond District'): 11,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Chinatown', 'Mission District'): 17,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Richmond District'): 20,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Chinatown'): 20,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Lisa': (1140, 120),          # 7:15 PM - 9:15 PM
    'Daniel': (495, 15),          # 8:15 AM - 11:00 AM
    'Elizabeth': (1110, 45),      # 9:15 PM - 10:15 PM
    'Steven': (270, 90),          # 4:30 PM - 8:45 PM
    'Timothy': (720, 90),         # 12:00 PM - 6:00 PM
    'Ashley': (1140, 60),         # 8:45 PM - 9:45 PM
    'Kevin': (720, 30),           # 12:00 PM - 7:00 PM
    'Betty': (75, 30),            # 1:15 PM - 3:45 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Lisa': 120,
    'Daniel': 15,
    'Elizabeth': 45,
    'Steven': 90,
    'Timothy': 90,
    'Ashley': 60,
    'Kevin': 30,
    'Betty': 30,
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

# Travel constraints from Mission District (arrival at 9:00 AM)
travel_times_to_friends = {
    'Lisa': travel_times[('Mission District', 'The Castro')],
    'Daniel': travel_times[('Mission District', 'Nob Hill')],
    'Elizabeth': travel_times[('Mission District', 'Presidio')],
    'Steven': travel_times[('Mission District', 'Marina District')],
    'Timothy': travel_times[('Mission District', 'Pacific Heights')],
    'Ashley': travel_times[('Mission District', 'Golden Gate Park')],
    'Kevin': travel_times[('Mission District', 'Chinatown')],
    'Betty': travel_times[('Mission District', 'Richmond District')],
}

# Add constraints for ensuring enough time to meet each friend after travel time
for friend, travel_time in travel_times_to_friends.items():
    solver.add(meeting_start[friend] >= 540 + travel_time)  # Must start after travel time (540 = 9:00 AM in minutes)

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