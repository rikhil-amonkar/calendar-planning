from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Mission District'): 25,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'North Beach'): 28,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'Alamo Square'): 17,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Alamo Square'): 19,
    ('Nob Hill', 'Sunset District'): 24,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Embarcadero'): 10,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Embarcadero'): 19,
    ('Mission District', 'Alamo Square'): 11,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Alamo Square'): 15,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Mission District'): 18,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Alamo Square'): 16,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Alamo Square'): 13,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Pacific Heights'): 11,
    ('Embarcadero', 'Mission District'): 20,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Richmond District'): 11,
    ('Alamo Square', 'Embarcadero'): 16,
}

# Define meeting times (in minutes after 9:00 AM)
meeting_times = {
    'Charles': (795, 105),   # Available from 1:15 PM to 3:00 PM (795 minutes after midnight)
    'Robert': (795, 90),      # Available from 1:15 PM to 5:30 PM (795 minutes after midnight)
    'Nancy': (825, 105),      # Available from 2:45 PM to 10:00 PM (825 minutes after midnight)
    'Brian': (930, 60),       # Available from 3:30 PM to 10:00 PM (930 minutes after midnight)
    'Kimberly': (1020, 75),   # Available from 5:00 PM to 7:45 PM (1020 minutes after midnight)
    'David': (825, 75),       # Available from 2:45 PM to 4:30 PM (825 minutes after midnight)
    'William': (750, 120),    # Available from 12:30 PM to 7:15 PM (750 minutes after midnight)
    'Jeffrey': (720, 45),     # Available from 12:00 PM to 7:15 PM (720 minutes after midnight)
    'Karen': (855, 60),       # Available from 2:15 PM to 8:45 PM (855 minutes after midnight)
    'Joshua': (945, 60)       # Available from 6:45 PM to 10:00 PM (945 minutes after midnight)
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

# Travel time constraints from Sunset District (arrival at 9:00 AM)
travel_times_to_friends = {
    'Charles': travel_times[('Sunset District', 'Presidio')],
    'Robert': travel_times[('Sunset District', 'Nob Hill')],
    'Nancy': travel_times[('Sunset District', 'Pacific Heights')],
    'Brian': travel_times[('Sunset District', 'Mission District')],
    'Kimberly': travel_times[('Sunset District', 'Marina District')],
    'David': travel_times[('Sunset District', 'North Beach')],
    'William': travel_times[('Sunset District', 'Russian Hill')],
    'Jeffrey': travel_times[('Sunset District', 'Richmond District')],
    'Karen': travel_times[('Sunset District', 'Embarcadero')],
    'Joshua': travel_times[('Sunset District', 'Alamo Square')],
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