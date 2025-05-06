from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'North Beach'): 29,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Union Square'): 11,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Golden Gate Park'): 18,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'The Castro'): 22,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Golden Gate Park'): 22,
    ('Union Square', 'Sunset District'): 26,
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'The Castro'): 19,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Union Square'): 22,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Karen': (1260, 60),        # 8:45 PM - 9:45 PM
    'Jessica': (1110, 60),      # 3:45 PM - 7:30 PM
    'Matthew': (435, 15),        # 7:30 AM - 3:15 PM
    'Michelle': (630, 75),       # 10:30 AM - 6:45 PM
    'Carol': (720, 90),          # 12:00 PM - 5:00 PM
    'Stephanie': (645, 30),      # 10:45 AM - 2:15 PM
    'Linda': (645, 90),          # 10:45 AM - 10:00 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Karen': 60,
    'Jessica': 60,
    'Matthew': 15,
    'Michelle': 75,
    'Carol': 90,
    'Stephanie': 30,
    'Linda': 90,
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting times based on friends' availability
for friend in meeting_times.keys():
    start_time, _ = meeting_times[friend]
    solver.add(meeting_start[friend] >= start_time)  # Must start after their available time
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])  # Calculate end time

# Travel time constraints from Sunset District (arrival at 9:00 AM)
travel_times_to_friends = {
    'Karen': travel_times[('Sunset District', 'Russian Hill')],
    'Jessica': travel_times[('Sunset District', 'The Castro')],
    'Matthew': travel_times[('Sunset District', 'Richmond District')],
    'Michelle': travel_times[('Sunset District', 'Marina District')],
    'Carol': travel_times[('Sunset District', 'North Beach')],
    'Stephanie': travel_times[('Sunset District', 'Union Square')],
    'Linda': travel_times[('Sunset District', 'Golden Gate Park')],
}

# Add constraints for ensuring enough time to meet each friend after traveling
for friend, travel_time in travel_times_to_friends.items():
    solver.add(meeting_start[friend] >= 540 + travel_time)  # Must start after 9:00 AM + travel time (540 = 9:00 AM in minutes)

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