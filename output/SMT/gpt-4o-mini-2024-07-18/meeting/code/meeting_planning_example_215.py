from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Richmond District', 'Bayview'): 26,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Jessica': (1050, 30),    # 4:45 PM - 7:00 PM
    'Sandra': (1080, 120),     # 6:30 PM - 9:45 PM
    'Jason': (240, 30),        # 4:00 PM - 4:45 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Jessica': 30,
    'Sandra': 120,
    'Jason': 30,
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting times based on friends' availability
for friend in meeting_times.keys():
    start_time, _ = meeting_times[friend]
    # Meeting start time must be greater than travel time plus arrival time
    solver.add(meeting_start[friend] >= start_time)  # Must be after the start time
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])  # Calculate end time

# Travel constraints from Bayview (arrival at 9:00 AM)
travel_times_to_friends = {
    'Jessica': travel_times[('Bayview', 'Embarcadero')],
    'Sandra': travel_times[('Bayview', 'Richmond District')],
    'Jason': travel_times[('Bayview', 'Fisherman\'s Wharf')],
}

# Add constraints for ensuring enough time to meet each friend after traveling
for friend, travel_time in travel_times_to_friends.items():
    solver.add(meeting_start[friend] >= travel_time)  # Must start after travel time

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