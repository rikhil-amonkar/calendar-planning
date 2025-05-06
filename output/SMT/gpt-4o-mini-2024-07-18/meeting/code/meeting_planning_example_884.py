from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Richmond District', 'Chinatown'): 20,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Bayview'): 27,
    ('Chinatown', 'Richmond District'): 20,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Bayview'): 20,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'North Beach'): 28,
    ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Bayview'): 22,
    ('Alamo Square', 'Richmond District'): 11,
    ('Alamo Square', 'Chinatown'): 15,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Bayview'): 16,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Bayview'): 19,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Bayview'): 25,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Bayview'): 21,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Bayview'): 31,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Chinatown'): 19,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'North Beach'): 22,
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Presidio'): 32,
    ('Bayview', 'Golden Gate Park'): 22,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Robert': (465, 120),        # 7:45 AM - 5:30 PM
    'David': (750, 45),          # 12:30 PM - 7:45 PM
    'Matthew': (525, 90),        # 8:45 AM - 1:45 PM
    'Jessica': (570, 45),        # 9:30 AM - 6:45 PM
    'Melissa': (435, 45),        # 7:15 AM - 4:45 PM
    'Mark': (855, 45),           # 3:15 PM - 5:00 PM
    'Deborah': (1140, 45),       # 7:00 PM - 7:45 PM
    'Karen': (1170, 120),        # 7:30 PM - 10:00 PM
    'Laura': (1110, 15),         # 9:15 PM - 10:15 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Robert': 120,
    'David': 45,
    'Matthew': 90,
    'Jessica': 45,
    'Melissa': 45,
    'Mark': 45,
    'Deborah': 45,
    'Karen': 120,
    'Laura': 15,
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting times based on friends' availability
for friend in meeting_times:
    start_time, _ = meeting_times[friend]
    solver.add(meeting_start[friend] >= start_time)  # Must start after their available time
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])  # Calculate end time

# Travel time constraints from Richmond District (arrival at 9:00 AM)
travel_times_to_friends = {
    'Robert': travel_times[('Richmond District', 'Chinatown')],
    'David': travel_times[('Richmond District', 'Sunset District')],
    'Matthew': travel_times[('Richmond District', 'Alamo Square')],
    'Jessica': travel_times[('Richmond District', 'Financial District')],
    'Melissa': travel_times[('Richmond District', 'North Beach')],
    'Mark': travel_times[('Richmond District', 'Embarcadero')],
    'Deborah': travel_times[('Richmond District', 'Presidio')],
    'Karen': travel_times[('Richmond District', 'Golden Gate Park')],
    'Laura': travel_times[('Richmond District', 'Bayview')],
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