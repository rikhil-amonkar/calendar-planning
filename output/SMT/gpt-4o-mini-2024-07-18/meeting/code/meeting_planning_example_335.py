from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Mission District'): 15,
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Mission District'): 18,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Mission District'): 17,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Mission District'): 10,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Financial District'): 17,
    ('Mission District', 'Alamo Square'): 11,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Helen': (540, 15),         # 9:00 AM - 5:00 PM
    'Betty': (1140, 90),        # 7:00 PM - 9:45 PM
    'Amanda': (1170, 60),       # 7:45 PM - 9:00 PM
    'Kevin': (645, 45),         # 10:45 AM - 2:45 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Helen': 15,
    'Betty': 90,
    'Amanda': 60,
    'Kevin': 45,
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting times based on friends' availability
for friend in meeting_times.keys():
    start_time, _ = meeting_times[friend]
    solver.add(meeting_start[friend] >= start_time)  # Must start after their available time
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])  # Calculate end time

# Travel time constraints from Pacific Heights (arrival at 9:00 AM)
travel_times_to_friends = {
    'Helen': travel_times[('Pacific Heights', 'North Beach')],
    'Betty': travel_times[('Pacific Heights', 'Financial District')],
    'Amanda': travel_times[('Pacific Heights', 'Alamo Square')],
    'Kevin': travel_times[('Pacific Heights', 'Mission District')],
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
    for friend in meeting_times.keys():
        start = model[meeting_start[friend]].as_long() 
        end = model[meeting_end[friend]].as_long()
        print(f"{friend}: Start at {start} minutes after midnight, End at {end} minutes after midnight")
else:
    print("SOLUTION: No valid meeting schedule found.")