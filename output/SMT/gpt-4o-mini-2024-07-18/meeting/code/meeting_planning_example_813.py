from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Mission District'): 20,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Mission District'): 20,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'Chinatown'): 19,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Mission District'): 13,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Mission District'): 14,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'Bayview'): 20,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Mission District'): 17,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Mission District'): 25,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Mission District'): 17,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'Embarcadero'): 19,
    ('Mission District', 'Bayview'): 14,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Financial District'): 15,
    ('Mission District', 'Haight-Ashbury'): 12,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Joshua': (585, 105),      # 9:45 AM - 6:00 PM
    'Jeffrey': (585, 75),       # 9:45 AM - 8:15 PM
    'Charles': (645, 120),      # 10:45 AM - 8:15 PM
    'Joseph': (450, 60),        # 7:00 AM - 3:30 PM
    'Elizabeth': (540, 45),     # 9:00 AM - 9:45 AM
    'Matthew': (660, 45),       # 11:00 AM - 7:30 PM
    'Carol': (645, 15),         # 10:45 AM - 11:15 AM
    'Paul': (915, 15),          # 7:15 PM - 8:30 PM
    'Rebecca': (900, 45)        # 5:00 PM - 9:45 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Joshua': 105,
    'Jeffrey': 75,
    'Charles': 120,
    'Joseph': 60,
    'Elizabeth': 45,
    'Matthew': 45,
    'Carol': 15,
    'Paul': 15,
    'Rebecca': 45,
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

# Travel constraints from Marina District (arrival at 9:00 AM)
travel_times_to_friends = {
    'Joshua': travel_times[('Marina District', 'Embarcadero')],
    'Jeffrey': travel_times[('Marina District', 'Bayview')],
    'Charles': travel_times[('Marina District', 'Union Square')],
    'Joseph': travel_times[('Marina District', 'Chinatown')],
    'Elizabeth': travel_times[('Marina District', 'Sunset District')],
    'Matthew': travel_times[('Marina District', 'Golden Gate Park')],
    'Carol': travel_times[('Marina District', 'Financial District')],
    'Paul': travel_times[('Marina District', 'Haight-Ashbury')],
    'Rebecca': travel_times[('Marina District', 'Mission District')],
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