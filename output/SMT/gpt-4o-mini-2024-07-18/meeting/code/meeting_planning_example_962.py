from z3 import *

# Define travel distances (in minutes)
travel_times = {
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Sunset District'): 17,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Sunset District'): 19,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Sunset District'): 15,
    ('North Beach', 'The Castro'): 23,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Sunset District'): 27,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Sunset District'): 30,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Sunset District'): 11,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Richmond District'): 11,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Sunset District'): 16,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Sunset District'): 30,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'North Beach'): 28,
    ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Financial District'): 30,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Elizabeth': (1140, 105),          # 7:00 PM - 8:45 PM
    'Joshua': (510, 105),              # 8:30 AM - 1:15 PM
    'Timothy': (1170, 90),             # 7:45 PM - 10:00 PM
    'David': (645, 30),                # 10:45 AM - 12:30 PM
    'Kimberly': (1050, 75),            # 4:45 PM - 9:30 PM
    'Lisa': (1020, 45),                # 5:30 PM - 9:45 PM
    'Ronald': (450, 90),               # 8:00 AM - 9:30 AM
    'Stephanie': (210, 30),            # 3:30 PM - 4:30 PM
    'Helen': (1020, 45),               # 5:30 PM - 6:30 PM
    'Laura': (1050, 90),               # 5:45 PM - 9:15 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Elizabeth': 105,
    'Joshua': 105,
    'Timothy': 90,
    'David': 30,
    'Kimberly': 75,
    'Lisa': 45,
    'Ronald': 90,
    'Stephanie': 30,
    'Helen': 45,
    'Laura': 90,
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

# Travel times from The Castro (arrival at 9:00 AM)
travel_times_to_friends = {
    'Elizabeth': travel_times[('The Castro', 'Marina District')],
    'Joshua': travel_times[('The Castro', 'Presidio')],
    'Timothy': travel_times[('The Castro', 'North Beach')],
    'David': travel_times[('The Castro', 'Embarcadero')],
    'Kimberly': travel_times[('The Castro', 'Haight-Ashbury')],
    'Lisa': travel_times[('The Castro', 'Golden Gate Park')],
    'Ronald': travel_times[('The Castro', 'Richmond District')],
    'Stephanie': travel_times[('The Castro', 'Alamo Square')],
    'Helen': travel_times[('The Castro', 'Financial District')],
    'Laura': travel_times[('The Castro', 'Sunset District')],
}

# Add constraints for ensuring enough time to meet each friend after travel time
for friend, travel_time in travel_times_to_friends.items():
    solver.add(meeting_start[friend] >= 540 + travel_time)  # Must start after travel time (540 = 9:00 AM in minutes)

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