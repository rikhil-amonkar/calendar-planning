from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Golden Gate Park', 'Sunset District'): 10,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Joshua': (1260, 15),  # 8:45 PM - 9:45 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Joshua': 15,
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

# Travel constraints from Sunset District (arrival at 9:00 AM)
solver.add(meeting_start['Joshua'] >= 540 + travel_times[('Sunset District', 'Golden Gate Park')])  # Must start after arrival and travel

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