from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Marina District'): 11,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Marina District'): 11,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Marina District'): 7,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Marina District'): 9,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Marina District'): 12,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Marina District'): 18,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Marina District'): 12,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Marina District'): 15,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Financial District'): 17,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Karen': (1260, 45),       # 9:00 PM - 9:45 PM
    'Jessica': (1050, 90),     # 1:45 PM - 9:00 PM
    'Brian': (990, 60),        # 3:30 PM - 9:45 PM
    'Kenneth': (585, 30),      # 9:45 AM - 9:00 PM
    'Jason': (495, 75),        # 8:15 AM - 11:45 AM
    'Stephanie': (945, 105),   # 2:45 PM - 6:45 PM
    'Kimberly': (585, 75),     # 9:45 AM - 7:30 PM
    'Steven': (435, 60),       # 7:15 AM - 9:15 PM
    'Mark': (615, 75)          # 10:15 AM - 1:00 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Karen': 45,
    'Jessica': 90,
    'Brian': 60,
    'Kenneth': 30,
    'Jason': 75,
    'Stephanie': 105,
    'Kimberly': 75,
    'Steven': 60,
    'Mark': 75
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting times based on friends' availability
for friend in meeting_times.keys():
    start_time, _ = meeting_times[friend]
    solver.add(meeting_start[friend] >= start_time)  # Must be after their available time
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])  # Calculate end time

# Travel time constraints from Presidio (arrival at 9:00 AM)
travel_times_to_friends = {
    'Karen': travel_times[('Presidio', 'Haight-Ashbury')],
    'Jessica': travel_times[('Presidio', 'Nob Hill')],
    'Brian': travel_times[('Presidio', 'Russian Hill')],
    'Kenneth': travel_times[('Presidio', 'North Beach')],
    'Jason': travel_times[('Presidio', 'Chinatown')],
    'Stephanie': travel_times[('Presidio', 'Union Square')],
    'Kimberly': travel_times[('Presidio', 'Embarcadero')],
    'Steven': travel_times[('Presidio', 'Financial District')],
    'Mark': travel_times[('Presidio', 'Marina District')],
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