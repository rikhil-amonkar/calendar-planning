from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Mission District'): 24,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Mission District'): 10,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Mission District'): 16,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Golden Gate Park'): 17,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Charles': (1110, 90),       # 6:00 PM - 8:45 PM
    'Margaret': (540, 30),       # 9:00 AM - 4:00 PM
    'Daniel': (510, 15),         # 8:00 AM - 1:30 PM
    'Stephanie': (1140, 90),     # 8:30 PM - 10:00 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Charles': 90,
    'Margaret': 30,
    'Daniel': 15,
    'Stephanie': 90,
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
travel_times_to_friends = {
    'Charles': travel_times[('Sunset District', 'Alamo Square')],
    'Margaret': travel_times[('Sunset District', 'Russian Hill')],
    'Daniel': travel_times[('Sunset District', 'Golden Gate Park')],
    'Stephanie': travel_times[('Sunset District', 'Mission District')],
}

# Add constraints for ensuring enough time to meet each friend after travel time
for friend, travel_time in travel_times_to_friends.items():
    solver.add(meeting_start[friend] >= 540 + travel_time)  # Must start after travel time (540 = 9:00 AM in minutes)

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