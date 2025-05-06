from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Financial District'): 23,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Financial District'): 22,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Richmond District'): 21,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Emily': (885, 105),          # 4:15 PM - 9:00 PM
    'Joseph': (1050, 120),        # 5:15 PM - 10:00 PM
    'Melissa': (855, 75),         # 3:45 PM - 9:45 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Emily': 105,
    'Joseph': 120,
    'Melissa': 75,
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting times based on friends' availability
for friend in meeting_times.keys():
    start_time, _ = meeting_times[friend]
    solver.add(meeting_start[friend] >= start_time)  # Must be after their availability
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])  # Calculate end time

# Travel constraints from Fisherman's Wharf (arrival at 9:00 AM)
travel_times_to_friends = {
    'Emily': travel_times[('Fisherman\'s Wharf', 'Presidio')],
    'Joseph': travel_times[('Fisherman\'s Wharf', 'Richmond District')],
    'Melissa': travel_times[('Fisherman\'s Wharf', 'Financial District')],
}

# Add constraints for meeting start times ensuring enough time for travel
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