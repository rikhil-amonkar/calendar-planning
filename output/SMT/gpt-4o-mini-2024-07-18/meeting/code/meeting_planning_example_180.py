from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('North Beach', 'Mission District'): 18,
    ('North Beach', 'The Castro'): 22,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'The Castro'): 7,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Mission District'): 7,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'James': (765, 75),  # 12:45 PM - 2:00 PM (765 minutes after midnight)
    'Robert': (765, 30), # 12:45 PM - 3:15 PM (765 minutes after midnight)
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'James': 75,
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

# Travel time constraints from North Beach (arrival at 9:00 AM)
travel_times_to_friends = {
    'James': travel_times[('North Beach', 'Mission District')],
    'Robert': travel_times[('North Beach', 'The Castro')],
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