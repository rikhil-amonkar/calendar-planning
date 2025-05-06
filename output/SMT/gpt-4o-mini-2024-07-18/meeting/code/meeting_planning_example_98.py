from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Alamo Square', 'Richmond District'): 12,
    ('Richmond District', 'Alamo Square'): 13,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Timothy': (1260, 45),      # 8:45 PM - 9:30 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Timothy': 45,
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting times based on Timothy's availability
for friend in meeting_times.keys():
    start_time, _ = meeting_times[friend]
    solver.add(meeting_start[friend] >= start_time)  # Must start after his available time
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])  # Calculate end time

# Travel time constraints from Alamo Square (arrival at 9:00 AM)
travel_time_to_timothy = travel_times[('Alamo Square', 'Richmond District')]

# Add constraints for ensuring enough time to meet Timothy after traveling
solver.add(meeting_start['Timothy'] >= 540 + travel_time_to_timothy)  # Must start after 9:00 AM + travel time (540 = 9:00 AM in minutes)

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