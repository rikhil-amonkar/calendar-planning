from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Financial District'): 30,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Presidio'): 18,
    ('Alamo Square', 'Financial District'): 17,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Financial District'): 11,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Alamo Square'): 18,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Financial District'): 23,
    ('Financial District', 'Sunset District'): 31,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Russian Hill'): 10,
    ('Financial District', 'Presidio'): 22,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Kevin': (1230, 75),        # 8:15 PM to 9:30 PM
    'Kimberly': (525, 30),      # 8:45 AM to 12:30 PM
    'Joseph': (1110, 45),       # 6:30 PM to 7:15 PM
    'Thomas': (1145, 45),       # 7:00 PM to 9:45 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Kevin': 75,
    'Kimberly': 30,
    'Joseph': 45,
    'Thomas': 45,
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

# Travel time constraints from Sunset District (arrival at 9:00 AM)
travel_times_to_friends = {
    'Kevin': travel_times[('Sunset District', 'Alamo Square')],
    'Kimberly': travel_times[('Sunset District', 'Russian Hill')],
    'Joseph': travel_times[('Sunset District', 'Presidio')],
    'Thomas': travel_times[('Sunset District', 'Financial District')],
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