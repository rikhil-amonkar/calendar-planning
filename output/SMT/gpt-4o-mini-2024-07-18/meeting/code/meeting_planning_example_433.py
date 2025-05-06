from z3 import *

# Define places
places = [
    'Nob Hill', 'Richmond District', 'Financial District',
    'North Beach', 'The Castro', 'Golden Gate Park'
]

# Define travel times (in minutes)
travel_times = {
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'The Castro'): 23,
    ('Financial District', 'Golden Gate Park'): 23,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'The Castro'): 22,
    ('North Beach', 'Golden Gate Park'): 22,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Financial District'): 20,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'The Castro'): 13,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Emily': (1140, 120),      # 7:00 PM - 9:00 PM (1140 minutes after 9:00 AM)
    'Margaret': (1050, 75),    # 4:30 PM - 8:15 PM (1050 minutes after 9:00 AM)
    'Ronald': (1110, 45),       # 6:30 PM - 7:30 PM (1110 minutes after 9:00 AM)
    'Deborah': (795, 90),       # 1:45 PM - 9:15 PM (795 minutes after 9:00 AM)
    'Jeffrey': (675, 120)       # 11:15 AM - 2:30 PM (675 minutes after 9:00 AM)
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Emily': 15,
    'Margaret': 75,
    'Ronald': 45,
    'Deborah': 90,
    'Jeffrey': 120,
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting times based on friends' availability
for friend in meeting_times.keys():
    start_time, _ = meeting_times[friend]
    solver.add(meeting_start[friend] >= start_time)
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])

# Travel constraints from Nob Hill (arrival at 9:00 AM)
travel_times_to_friends = {
    'Emily': travel_times[('Nob Hill', 'Richmond District')],
    'Margaret': travel_times[('Nob Hill', 'Financial District')],
    'Ronald': travel_times[('Nob Hill', 'North Beach')],
    'Deborah': travel_times[('Nob Hill', 'The Castro')],
    'Jeffrey': travel_times[('Nob Hill', 'Golden Gate Park')],
}

# Add constraints for ensuring enough time to meet each friend
for friend, travel_time in travel_times_to_friends.items():
    solver.add(meeting_start[friend] >= travel_time)

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
        print(f"{friend}: Start at {start} minutes after 9:00 AM, End at {end} minutes after 9:00 AM")
else:
    print("SOLUTION: No valid meeting schedule found.")