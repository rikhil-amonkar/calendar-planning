from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Stephanie': (495, 90),       # 8:15 AM - 1:45 PM
    'Sandra': (780, 15),          # 1:00 PM - 7:30 PM
    'Richard': (435, 75),         # 7:15 AM - 10:15 AM
    'Brian': (735, 120),          # 12:15 PM - 4:00 PM
    'Jason': (510, 60),           # 8:30 AM - 5:45 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Stephanie': 90,
    'Sandra': 15,
    'Richard': 75,
    'Brian': 120,
    'Jason': 60,
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

# Travel constraints from Haight-Ashbury (arrival at 9:00 AM)
travel_times_to_friends = {
    'Stephanie': travel_times[('Haight-Ashbury', 'Mission District')],
    'Sandra': travel_times[('Haight-Ashbury', 'Bayview')],
    'Richard': travel_times[('Haight-Ashbury', 'Pacific Heights')],
    'Brian': travel_times[('Haight-Ashbury', 'Russian Hill')],
    'Jason': travel_times[('Haight-Ashbury', 'Fisherman\'s Wharf')],
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