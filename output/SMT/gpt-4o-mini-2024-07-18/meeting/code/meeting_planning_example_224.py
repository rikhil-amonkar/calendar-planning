from z3 import *

# Define places
places = [
    'Fisherman\'s Wharf', 'Golden Gate Park',
    'Presidio', 'Richmond District'
]

# Define travel times (in minutes)
travel_times = {
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Richmond District'): 7,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Presidio'): 7,
}

# Define availability times and meeting durations (in minutes after 9:00 AM)
meeting_times = {
    'Melissa': (510, 15),      # 8:30 AM - 8:00 PM (510 minutes after 9:00 AM)
    'Nancy': (1140, 105),      # 7:45 PM - 10:00 PM (1140 minutes after 9:00 AM)
    'Emily': (945, 120),        # 4:45 PM - 10:00 PM (945 minutes after 9:00 AM)
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Melissa': 15,
    'Nancy': 105,
    'Emily': 120,
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting times based on friends' availability
for friend in meeting_times.keys():
    start_time, _ = meeting_times[friend]
    solver.add(meeting_start[friend] >= start_time)
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])

# Travel constraints from Fisherman's Wharf (arrival at 9:00 AM)
travel_times_to_friends = {
    'Melissa': travel_times[('Fisherman\'s Wharf', 'Golden Gate Park')],
    'Nancy': travel_times[('Fisherman\'s Wharf', 'Presidio')],
    'Emily': travel_times[('Fisherman\'s Wharf', 'Richmond District')],
}

# Add constraints for ensuring enough time to meet each friend
for friend, travel_time in travel_times_to_friends.items():
    solver.add(meeting_start[friend] >= travel_time)

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