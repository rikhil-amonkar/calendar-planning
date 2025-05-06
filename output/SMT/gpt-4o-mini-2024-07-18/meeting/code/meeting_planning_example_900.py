from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Chinatown'): 20,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Bayview'): 27,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Chinatown'): 22,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Bayview'): 19,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Bayview'): 19,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Bayview'): 27,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Bayview'): 22,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Bayview'): 14,
    ('Chinatown', 'Richmond District'): 20,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Mission District'): 17,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Bayview'): 20,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Bayview'): 23,
    ('Alamo Square', 'Richmond District'): 11,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Chinatown'): 15,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Bayview'): 16,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'The Castro'): 19,
    ('Bayview', 'Nob Hill'): 20,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Chinatown'): 19,
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Alamo Square'): 16,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Matthew': (1020, 45),   # 4:30 PM - 8:00 PM
    'Rebecca': (915, 105),    # 3:15 PM - 7:15 PM
    'Brian': (1350, 30),      # 2:15 PM - 10:00 PM
    'Emily': (675, 15),       # 11:15 AM - 7:45 PM
    'Karen': (705, 30),       # 11:45 AM - 5:30 PM
    'Stephanie': (780, 75),   # 1:00 PM - 3:45 PM
    'James': (870, 120),       # 2:30 PM - 7:00 PM
    'Steven': (840, 30),      # 2:00 PM - 8:00 PM
    'Elizabeth': (780, 120),  # 1:00 PM - 5:15 PM
    'William': (1110, 90),    # 6:15 PM - 8:15 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Matthew': 45,
    'Rebecca': 105,
    'Brian': 30,
    'Emily': 15,
    'Karen': 30,
    'Stephanie': 75,
    'James': 120,
    'Steven': 30,
    'Elizabeth': 120,
    'William': 90,
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting times based on friends' availability
for friend in meeting_times.keys():
    start_time, _ = meeting_times[friend]
    solver.add(meeting_start[friend] >= start_time)  # Must start after their availability begins
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])  # Calculate end time

# Travel time constraints from Richmond District (arrival at 9:00 AM)
travel_times_to_friends = {
    'Matthew': travel_times[('Richmond District', 'The Castro')],
    'Rebecca': travel_times[('Richmond District', 'Nob Hill')],
    'Brian': travel_times[('Richmond District', 'Marina District')],
    'Emily': travel_times[('Richmond District', 'Pacific Heights')],
    'Karen': travel_times[('Richmond District', 'Haight-Ashbury')],
    'Stephanie': travel_times[('Richmond District', 'Mission District')],
    'James': travel_times[('Richmond District', 'Chinatown')],
    'Steven': travel_times[('Richmond District', 'Russian Hill')],
    'Elizabeth': travel_times[('Richmond District', 'Alamo Square')],
    'William': travel_times[('Richmond District', 'Bayview')],
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