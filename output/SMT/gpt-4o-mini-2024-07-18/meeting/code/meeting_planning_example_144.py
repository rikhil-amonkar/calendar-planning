from z3 import *

# Define travel distances (in minutes)
travel_times = {
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Financial District'): 20,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Financial District'): 17,
    ('Financial District', 'The Castro'): 23,
    ('Financial District', 'Mission District'): 17,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Laura': (735, 75),    # 12:15 PM - 7:45 PM
    'Anthony': (750, 30),  # 12:30 PM - 2:45 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Laura': 75,
    'Anthony': 30,
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

# Travel time constraints from The Castro (arrival at 9:00 AM)
travel_times_to_friends = {
    'Laura': travel_times[('The Castro', 'Mission District')],
    'Anthony': travel_times[('The Castro', 'Financial District')],
}

# Add constraints for ensuring enough time to meet each friend after traveling
for friend, travel_time in travel_times_to_friends.items():
    solver.add(meeting_start[friend] >= 540 + travel_time)  # Start after 9:00 AM + travel time (540 = 9:00 AM in minutes)

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