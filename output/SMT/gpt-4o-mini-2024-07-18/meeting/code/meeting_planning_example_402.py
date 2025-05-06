from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Union Square'): 17,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Union Square'): 30,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Union Square'): 16,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Sunset District'): 31,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Union Square'): 9,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Sunset District'): 26,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Financial District'): 9,
}

# Define friends and their availability times (in minutes after 9:00 AM)
meeting_times = {
    'Sarah': (1020, 105),     # Available from 5:00 PM
    'Patricia': (1020, 45),   # Available from 5:00 PM to 7:45 PM
    'Matthew': (555, 15),     # Available from 9:15 AM to 12:00 PM
    'Joseph': (1350, 30),     # Available from 2:15 PM to 6:45 PM
    'Robert': (615, 15),      # Available from 10:15 AM to 9:45 PM
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting times based on friends' availability
for friend, (start_time, duration) in meeting_times.items():
    solver.add(meeting_start[friend] >= start_time)  # Must start after their available time
    solver.add(meeting_end[friend] == meeting_start[friend] + duration)  # Calculate end time

# Travel time constraints from Golden Gate Park (arrival at 9:00 AM)
travel_times_to_friends = {
    'Sarah': travel_times[('Golden Gate Park', 'Haight-Ashbury')],
    'Patricia': travel_times[('Golden Gate Park', 'Sunset District')],
    'Matthew': travel_times[('Golden Gate Park', 'Marina District')],
    'Joseph': travel_times[('Golden Gate Park', 'Financial District')],
    'Robert': travel_times[('Golden Gate Park', 'Union Square')],
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
    for friend in meeting_times:
        start = model[meeting_start[friend]].as_long()
        end = model[meeting_end[friend]].as_long()
        print(f"{friend}: Start at {start} minutes after midnight, End at {end} minutes after midnight")
else:
    print("SOLUTION: No valid meeting schedule found.")