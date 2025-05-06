from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'William': (1110, 105),        # 6:30 PM - 8:45 PM
    'Michelle': (495, 15),         # 8:15 AM - 2:00 PM
    'George': (630, 30),           # 10:30 AM - 6:45 PM
    'Robert': (540, 30),           # 9:00 AM - 1:45 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'William': 105,
    'Michelle': 15,
    'George': 30,
    'Robert': 30,
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

# Travel time constraints from Sunset District (arrival at 9:00 AM)
travel_times_to_friends = {
    'William': travel_times[('Sunset District', 'Russian Hill')],
    'Michelle': travel_times[('Sunset District', 'Chinatown')],
    'George': travel_times[('Sunset District', 'Presidio')],
    'Robert': travel_times[('Sunset District', 'Fisherman\'s Wharf')],
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