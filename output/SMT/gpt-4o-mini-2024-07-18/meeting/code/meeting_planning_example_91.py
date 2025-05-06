from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Russian Hill', 'Richmond District'): 14,
    ('Richmond District', 'Russian Hill'): 13,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Daniel': (1140, 75),  # 7:00 PM - 8:15 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Daniel': 75,
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting times based on friend availability
for friend in meeting_times.keys():
    start_time, _ = meeting_times[friend]
    solver.add(meeting_start[friend] >= start_time)  # Must start after their available time
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])  # Calculate the end time

# Travel time constraint from Russian Hill (arrival at 9:00 AM)
solver.add(meeting_start['Daniel'] >= 540 + travel_times[('Russian Hill', 'Richmond District')])  # Must start after 9:00 AM + travel time (540 = 9:00 AM in minutes)

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