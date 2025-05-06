from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
}

# Define meeting times and durations (in minutes after 9:00 AM)
# Time is in minutes after 9:00 AM
meeting_times = {
    'Betty': (615, 45),       # 10:15 AM - 9:30 PM
    'David': (780, 90),       # 1:00 PM - 8:15 PM
    'Barbara': (555, 120),    # 9:15 AM - 8:15 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Betty': 45,
    'David': 90,
    'Barbara': 120,
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting times based on friends' availability
for friend in meeting_times.keys():
    start_time, _ = meeting_times[friend]
    solver.add(meeting_start[friend] >= start_time)  # Must be after the start time
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])  # Calculate end time

# Travel constraints from Embarcadero (arrival at 9:00 AM)
travel_times_to_friends = {
    'Betty': travel_times[('Embarcadero', 'Presidio')],
    'David': travel_times[('Embarcadero', 'Richmond District')],
    'Barbara': travel_times[('Embarcadero', 'Fisherman\'s Wharf')],
}

# Add constraints for ensuring enough time to meet each friend
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