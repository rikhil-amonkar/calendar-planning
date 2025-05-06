from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Fisherman\'s Wharf'): 11,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Pacific Heights'): 11,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Pacific Heights'): 8,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Jeffrey': (480, 105),       # 8:00 AM - 10:00 AM
    'Steven': (870, 45),         # 1:30 PM - 10:00 PM
    'Barbara': (1080, 30),       # 6:00 PM - 9:30 PM
    'John': (540, 15),           # 9:00 AM - 1:30 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Jeffrey': 105,
    'Steven': 45,
    'Barbara': 30,
    'John': 15,
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
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])  # Calculate the end time

# Travel time constraints from Nob Hill (arrival at 9:00 AM)
travel_times_to_friends = {
    'Jeffrey': travel_times[('Nob Hill', 'Presidio')],
    'Steven': travel_times[('Nob Hill', 'North Beach')],
    'Barbara': travel_times[('Nob Hill', 'Fisherman\'s Wharf')],
    'John': travel_times[('Nob Hill', 'Pacific Heights')],
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