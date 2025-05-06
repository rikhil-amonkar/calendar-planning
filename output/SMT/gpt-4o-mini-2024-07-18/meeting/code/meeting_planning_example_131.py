from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Marina District'): 6,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Marina District'): 10,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Presidio'): 10,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Jason': (600, 90),    # Available from 10:00 AM to 4:15 PM (600 minutes after midnight)
    'Kenneth': (930, 45)   # Available from 3:30 PM to 4:45 PM (930 minutes after midnight)
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting times based on friends' availability
for friend, (start_time, duration) in meeting_times.items():
    solver.add(meeting_start[friend] >= start_time)  # Must start after their available time
    solver.add(meeting_end[friend] == meeting_start[friend] + duration)  # Calculate end time

# Travel time constraints from Pacific Heights (arrival at 9:00 AM)
travel_times_to_friends = {
    'Jason': travel_times[('Pacific Heights', 'Presidio')],
    'Kenneth': travel_times[('Pacific Heights', 'Marina District')],
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