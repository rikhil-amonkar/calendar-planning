from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Russian Hill'): 18,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Russian Hill'): 14,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Russian Hill'): 24,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Russian Hill'): 15,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Golden Gate Park'): 21,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Rebecca': (1115, 60),        # 6:15 PM - 8:45 PM
    'Linda': (930, 30),           # 3:30 PM - 7:45 PM
    'Elizabeth': (1015, 105),     # 5:15 PM - 7:30 PM
    'William': (75, 30),          # 1:15 PM - 7:30 PM
    'Robert': (135, 45),          # 2:15 PM - 9:30 PM
    'Mark': (600, 75)             # 10:00 AM - 9:15 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Rebecca': 60,
    'Linda': 30,
    'Elizabeth': 105,
    'William': 30,
    'Robert': 45,
    'Mark': 75,
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

# Travel constraints from The Castro (arrival at 9:00 AM)
travel_times_to_friends = {
    'Rebecca': travel_times[('The Castro', 'Presidio')],
    'Linda': travel_times[('The Castro', 'Sunset District')],
    'Elizabeth': travel_times[('The Castro', 'Haight-Ashbury')],
    'William': travel_times[('The Castro', 'Mission District')],
    'Robert': travel_times[('The Castro', 'Golden Gate Park')],
    'Mark': travel_times[('The Castro', 'Russian Hill')],
}

# Add constraints for ensuring enough time to meet each friend after traveling
for friend, travel_time in travel_times_to_friends.items():
    solver.add(meeting_start[friend] >= travel_time)  # Meeting can only start after travel time

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