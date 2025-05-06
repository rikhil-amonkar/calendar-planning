from z3 import *

# Define places
places = [
    'Financial District', 'Chinatown', 'Golden Gate Park'
]

# Define travel times (in minutes)
travel_times = {
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Chinatown'): 23,
}

# Define availability times and minimum meeting durations (in minutes after 9:00 AM)
meeting_times = {
    'Kenneth': (720, 180),  # 12:00 PM - 3:00 PM
    'Barbara': (495, 570)    # 8:15 AM - 7:00 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Kenneth': 90,
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
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])

# Travel constraints from Financial District (arrival at 9:00 AM)
# Meeting Kenneth in Chinatown
travel_time_to_ken = travel_times[('Financial District', 'Chinatown')]
solver.add(meeting_start['Kenneth'] >= travel_time_to_ken)

# Meeting Barbara in Golden Gate Park
travel_time_to_barbara = travel_times[('Financial District', 'Golden Gate Park')]
solver.add(meeting_start['Barbara'] >= travel_time_to_barbara)

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