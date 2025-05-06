from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Presidio'): 18,
    ('Alamo Square', 'Chinatown'): 16,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Embarcadero'): 17,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Presidio', 'Alamo Square'): 18,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Embarcadero'): 31,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Chinatown'): 20,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Embarcadero'): 25,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Emily': (735, 105),       # 12:15 PM - 2:15 PM
    'Mark': (945, 60),         # 2:45 PM - 7:30 PM
    'Deborah': (450, 45),      # 7:30 AM - 3:30 PM
    'Margaret': (1140, 60),    # 9:30 PM - 10:30 PM
    'George': (450, 60),       # 7:30 AM - 2:15 PM
    'Andrew': (1115, 75),      # 8:15 PM - 10:00 PM
    'Steven': (675, 105)       # 11:15 AM - 9:15 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Emily': 105,
    'Mark': 60,
    'Deborah': 45,
    'Margaret': 60,
    'George': 60,
    'Andrew': 75,
    'Steven': 105,
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

# Travel constraints from Alamo Square (arrival at 9:00 AM)
travel_times_to_friends = {
    'Emily': travel_times[('Alamo Square', 'Russian Hill')],
    'Mark': travel_times[('Alamo Square', 'Presidio')],
    'Deborah': travel_times[('Alamo Square', 'Chinatown')],
    'Margaret': travel_times[('Alamo Square', 'Sunset District')],
    'George': travel_times[('Alamo Square', 'The Castro')],
    'Andrew': travel_times[('Alamo Square', 'Embarcadero')],
    'Steven': travel_times[('Alamo Square', 'Golden Gate Park')],
}

# Add constraints for ensuring enough time to meet each friend after travel time
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