from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Mission District'): 18,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Nob Hill'): 7,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Mission District'): 18,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Nob Hill'): 8,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Nob Hill'): 9,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Nob Hill'): 12,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Golden Gate Park'): 17,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'James': (1200, 120),      # 8:00 PM - 10:00 PM
    'Robert': (735, 90),       # 12:15 PM - 4:45 PM
    'Jeffrey': (570, 120),     # 9:30 AM - 3:30 PM
    'Carol': (1110, 15),       # 6:15 PM - 9:15 PM
    'Mark': (690, 15),         # 11:30 AM - 5:45 PM
    'Sandra': (480, 15),       # 8:00 AM - 3:30 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'James': 120,
    'Robert': 90,
    'Jeffrey': 120,
    'Carol': 15,
    'Mark': 15,
    'Sandra': 15,
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting times based on friends' availability
for friend in meeting_times.keys():
    start_time, _ = meeting_times[friend]
    solver.add(meeting_start[friend] >= start_time)  # Must begin after their availability starts
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])  # Calculate end time

# Travel time constraints from North Beach (arrival at 9:00 AM)
travel_times_to_friends = {
    'James': travel_times[('North Beach', 'Pacific Heights')],
    'Robert': travel_times[('North Beach', 'Chinatown')],
    'Jeffrey': travel_times[('North Beach', 'Union Square')],
    'Carol': travel_times[('North Beach', 'Mission District')],
    'Mark': travel_times[('North Beach', 'Golden Gate Park')],
    'Sandra': travel_times[('North Beach', 'Nob Hill')],
}

# Add constraints for ensuring enough time to meet each friend after traveling
for friend, travel_time in travel_times_to_friends.items():
    solver.add(meeting_start[friend] >= 540 + travel_time)  # Must start after 9:00 AM + travel time

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