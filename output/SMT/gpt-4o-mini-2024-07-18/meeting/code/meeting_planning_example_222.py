from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Fisherman\'s Wharf'): 11,
    ('Nob Hill', 'Bayview'): 19,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Bayview'): 22,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Bayview', 'Nob Hill'): 20,
    ('Bayview', 'North Beach'): 21,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Helen': (540, 120),          # 7:00 AM - 4:45 PM
    'Kimberly': (1020, 45),       # 4:30 PM - 9:00 PM
    'Patricia': (1080, 120),      # 6:00 PM - 9:15 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Helen': 120,
    'Kimberly': 45,
    'Patricia': 120,
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

# Travel time constraints from Nob Hill (arrival at 9:00 AM)
travel_times_to_friends = {
    'Helen': travel_times[('Nob Hill', 'North Beach')],
    'Kimberly': travel_times[('Nob Hill', 'Fisherman\'s Wharf')],
    'Patricia': travel_times[('Nob Hill', 'Bayview')],
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