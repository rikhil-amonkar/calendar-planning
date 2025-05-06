from z3 import *

# Define locations
locations = ['Russian Hill', 'Richmond District']

# Define travel times (in minutes)
travel_times = {
    ('Russian Hill', 'Richmond District'): 14,
    ('Richmond District', 'Russian Hill'): 13,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Barbara': (795, 375),  # 1:15 PM - 6:15 PM
}

# Minimum meeting duration (in minutes)
minimum_duration = {
    'Barbara': 45,
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting times based on friends' availability
for friend in meeting_times.keys():
    start_time, end_time = meeting_times[friend]
    solver.add(meeting_start[friend] >= start_time, meeting_start[friend] <= end_time)
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_duration[friend])

# Travel constraints from Russian Hill (arrival at 9:00 AM)
travel_time_to_friend = travel_times[('Russian Hill', 'Richmond District')]
solver.add(meeting_start['Barbara'] >= travel_time_to_friend)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for friend in meeting_times.keys():
        start = model[meeting_start[friend]].as_long()
        end = model[meeting_end[friend]].as_long()
        print(f"{friend}: Start at {start} minutes after 9:00 AM, End at {end} minutes after 9:00 AM")
else:
    print("SOLUTION: No valid meeting schedule found.")