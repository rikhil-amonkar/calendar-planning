from z3 import *

# Define places
places = [
    'Union Square', 'Russian Hill', 'Alamo Square',
    'Haight-Ashbury', 'Marina District', 'Bayview',
    'Chinatown', 'Presidio', 'Sunset District'
]

# Define travel times (in minutes)
travel_times = {
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Sunset District'): 27,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Sunset District'): 23,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Chinatown'): 15,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Sunset District'): 16,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Sunset District'): 19,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Chinatown'): 19,
    ('Bayview', 'Presidio'): 32,
    ('Bayview', 'Sunset District'): 23,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Bayview'): 20,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Sunset District'): 29,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Sunset District'): 15,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Presidio'): 16,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Betty': (420, 285),       # 7:00 AM - 4:45 PM
    'Melissa': (570, 315),     # 9:30 AM - 5:15 PM
    'Joshua': (735, 420),      # 12:15 PM - 7:00 PM
    'Jeffrey': (735, 360),     # 12:15 PM - 6:00 PM
    'James': (450, 1200),      # 7:30 AM - 8:00 PM
    'Anthony': (705, 90),      # 11:45 AM - 1:30 PM
    'Timothy': (750, 165),     # 12:30 PM - 2:45 PM
    'Emily': (930, 120),        # 7:30 PM - 9:30 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Betty': 105,
    'Melissa': 105,
    'Joshua': 90,
    'Jeffrey': 45,
    'James': 90,
    'Anthony': 75,
    'Timothy': 90,
    'Emily': 120
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

# Travel constraints from Union Square (arrival at 9:00 AM)
travel_times_to_friends = {
    'Betty': travel_times[('Union Square', 'Russian Hill')],
    'Melissa': travel_times[('Union Square', 'Alamo Square')],
    'Joshua': travel_times[('Union Square', 'Haight-Ashbury')],
    'Jeffrey': travel_times[('Union Square', 'Marina District')],
    'James': travel_times[('Union Square', 'Bayview')],
    'Anthony': travel_times[('Union Square', 'Chinatown')],
    'Timothy': travel_times[('Union Square', 'Presidio')],
    'Emily': travel_times[('Union Square', 'Sunset District')],
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