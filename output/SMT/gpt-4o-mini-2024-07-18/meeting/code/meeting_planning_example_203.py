from z3 import *

# Define places
places = [
    'Financial District', 'Fisherman\'s Wharf', 'Pacific Heights', 'Mission District'
]

# Define travel times (in minutes)
travel_times = {
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Mission District'): 17,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Mission District'): 15,
    ('Mission District', 'Financial District'): 17,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Pacific Heights'): 16,
}

# Define availability times and meeting durations (in minutes after 9:00 AM)
meeting_times = {
    'David': (645, 15),      # 10:45 AM - 3:30 PM
    'Timothy': (540, 75),    # 9:00 AM - 3:30 PM
    'Robert': (735, 90)       # 12:15 PM - 7:45 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'David': 15,
    'Timothy': 75,
    'Robert': 90,
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

# Travel constraints from Financial District (arrival at 9:00 AM)
travel_times_to_friends = {
    'David': travel_times[('Financial District', 'Fisherman\'s Wharf')],
    'Timothy': travel_times[('Financial District', 'Pacific Heights')],
    'Robert': travel_times[('Financial District', 'Mission District')],
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