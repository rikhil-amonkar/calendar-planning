from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Embarcadero'): 19,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Mission District'): 20,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Patricia': (1110, 90),  # 6:30 PM - 9:45 PM
    'Ashley': (1260, 45),    # 8:30 PM - 9:15 PM
    'Timothy': (585, 120),    # 9:45 AM - 5:45 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Patricia': 90,
    'Ashley': 45,
    'Timothy': 120,
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

# Travel time constraints from Russian Hill (arrival at 9:00 AM)
travel_times_to_friends = {
    'Patricia': travel_times[('Russian Hill', 'Nob Hill')],
    'Ashley': travel_times[('Russian Hill', 'Mission District')],
    'Timothy': travel_times[('Russian Hill', 'Embarcadero')],
}

# Add constraints for ensuring enough time to meet each friend after traveling
for friend, travel_time in travel_times_to_friends.items():
    # Must start after arrival time (540 = 9:00 AM in minutes) plus travel time
    solver.add(meeting_start[friend] >= 540 + travel_time)

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