from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Bayview'): 23,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Bayview'): 31,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Richmond District'): 20,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Bayview'): 22,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Bayview'): 22,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Chinatown'): 20,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Presidio'): 31,
    ('Bayview', 'Chinatown'): 18,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Golden Gate Park'): 22,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Matthew': (660, 90),          # 11:00 AM - 9:00 PM
    'Margaret': (555, 90),         # 9:15 AM - 6:45 PM
    'Nancy': (1350, 15),           # 2:15 PM - 5:00 PM
    'Helen': (1170, 60),           # 7:45 PM - 10:00 PM
    'Rebecca': (1110, 60),         # 9:15 PM - 10:15 PM
    'Kimberly': (780, 120),        # 1:00 PM - 4:30 PM
    'Kenneth': (840, 60),          # 2:30 PM - 6:00 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Matthew': 90,
    'Margaret': 90,
    'Nancy': 15,
    'Helen': 60,
    'Rebecca': 60,
    'Kimberly': 120,
    'Kenneth': 60,
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting times based on availability
for friend in meeting_times.keys():
    start_time, _ = meeting_times[friend]
    solver.add(meeting_start[friend] >= start_time)  # Must start after their available time
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])  # Calculate end time

# Travel time constraints from Russian Hill (arrival at 9:00 AM)
travel_times_to_friends = {
    'Matthew': travel_times[('Russian Hill', 'Presidio')],
    'Margaret': travel_times[('Russian Hill', 'Chinatown')],
    'Nancy': travel_times[('Russian Hill', 'Pacific Heights')],
    'Helen': travel_times[('Russian Hill', 'Richmond District')],
    'Rebecca': travel_times[('Russian Hill', 'Fisherman\'s Wharf')],
    'Kimberly': travel_times[('Russian Hill', 'Golden Gate Park')],
    'Kenneth': travel_times[('Russian Hill', 'Bayview')],
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