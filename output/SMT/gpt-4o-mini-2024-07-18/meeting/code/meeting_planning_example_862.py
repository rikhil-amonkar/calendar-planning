from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Embarcadero'): 19,
    ('Mission District', 'Financial District'): 15,
    ('Mission District', 'Marina District'): 19,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Richmond District'): 11,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Marina District'): 15,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Marina District'): 11,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Marina District'): 7,
    ('North Beach', 'Mission District'): 18,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Marina District'): 9,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Marina District'): 9,
    ('Embarcadero', 'Mission District'): 20,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Marina District'): 12,
    ('Financial District', 'Mission District'): 17,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Marina District'): 15,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Financial District'): 17,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Laura': (1380, 75),        # 2:30 PM - 4:15 PM
    'Brian': (615, 30),         # 10:15 AM - 5:00 PM
    'Karen': (1080, 90),        # 6:00 PM - 8:15 PM
    'Stephanie': (615, 75),     # 10:15 AM - 4:00 PM
    'Helen': (690, 120),        # 11:30 AM - 9:45 PM
    'Sandra': (480, 30),        # 8:00 AM - 3:15 PM
    'Mary': (1080, 120),        # 4:45 PM - 6:45 PM
    'Deborah': (1140, 105),     # 7:00 PM - 8:45 PM
    'Elizabeth': (510, 105),    # 8:30 AM - 1:15 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Laura': 75,
    'Brian': 30,
    'Karen': 90,
    'Stephanie': 75,
    'Helen': 120,
    'Sandra': 30,
    'Mary': 120,
    'Deborah': 105,
    'Elizabeth': 105,
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

# Travel time constraints from Mission District (arrival at 9:00 AM)
travel_times_to_friends = {
    'Laura': travel_times[('Mission District', 'Alamo Square')],
    'Brian': travel_times[('Mission District', 'Presidio')],
    'Karen': travel_times[('Mission District', 'Russian Hill')],
    'Stephanie': travel_times[('Mission District', 'North Beach')],
    'Helen': travel_times[('Mission District', 'Golden Gate Park')],
    'Sandra': travel_times[('Mission District', 'Richmond District')],
    'Mary': travel_times[('Mission District', 'Embarcadero')],
    'Deborah': travel_times[('Mission District', 'Financial District')],
    'Elizabeth': travel_times[('Mission District', 'Marina District')],
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