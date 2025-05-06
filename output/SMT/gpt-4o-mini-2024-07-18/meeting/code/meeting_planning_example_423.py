from z3 import *

# Define places
places = [
    'Presidio', 'Richmond District', 'North Beach', 
    'Financial District', 'Golden Gate Park', 'Union Square'
]

# Define travel times (in minutes)
travel_times = {
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Union Square'): 22,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Union Square'): 21,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Union Square'): 7,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Union Square'): 9,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Golden Gate Park'): 22,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Jason': (780, 525),      # 1:00 PM - 8:45 PM -> 780 - 525 minutes after 9 AM
    'Melissa': (405, 495),    # 6:45 PM - 8:15 PM -> 405 - 495 minutes after 9 AM
    'Brian': (585, 1170),      # 9:45 AM - 9:45 PM -> 585 - 1170 minutes after 9 AM
    'Elizabeth': (525, 1170),  # 8:45 AM - 9:30 PM -> 525 - 1170 minutes after 9 AM
    'Laura': (135, 450)        # 2:15 PM - 7:30 PM -> 135 - 450 minutes after 9 AM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Jason': 90,
    'Melissa': 45,
    'Brian': 15,
    'Elizabeth': 105,
    'Laura': 75
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting start and end times based on availability
for friend in meeting_times.keys():
    start_time, end_time = meeting_times[friend]
    solver.add(meeting_start[friend] >= start_time, meeting_start[friend] <= end_time)
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])

# Travel constraints from Presidio (time from arrival at 9:00 AM)
travel_times_to_friends = {
    'Jason': travel_times[('Presidio', 'Richmond District')],
    'Melissa': travel_times[('Presidio', 'North Beach')],
    'Brian': travel_times[('Presidio', 'Financial District')],
    'Elizabeth': travel_times[('Presidio', 'Golden Gate Park')],
    'Laura': travel_times[('Presidio', 'Union Square')]
}

# Add constraints for ensuring enough travel time to meet each friend
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