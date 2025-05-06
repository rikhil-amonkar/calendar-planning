from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Financial District'): 19,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Financial District'): 5,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Betty': (1140, 15),       # 7:45 PM - 9:45 PM
    'Karen': (525, 30),        # 8:45 AM - 3:00 PM
    'Anthony': (1110, 105),    # 9:15 PM - 9:30 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Betty': 15,
    'Karen': 30,
    'Anthony': 105,
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

# Travel constraints from Bayview (arrival at 9:00 AM)
travel_times_to_friends = {
    'Betty': travel_times[('Bayview', 'Embarcadero')],
    'Karen': travel_times[('Bayview', 'Fisherman\'s Wharf')],
    'Anthony': travel_times[('Bayview', 'Financial District')],
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