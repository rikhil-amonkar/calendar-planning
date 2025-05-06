from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Russian Hill'): 8,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Russian Hill'): 18,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Russian Hill'): 13,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Richmond District'): 11,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Mission District'): 17,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Russian Hill'): 11,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Russian Hill'): 14,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Financial District'): 15,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Russian Hill'): 15,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Nob Hill'): 5,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Linda': (1080, 30),       # 6:00 PM - 10:00 PM
    'Kenneth': (825, 30),      # 2:45 PM - 4:15 PM
    'Kimberly': (1350, 30),    # 2:15 PM - 10:00 PM
    'Paul': (1260, 15),        # 9:00 PM - 9:30 PM
    'Carol': (615, 60),        # 10:15 AM - 12:00 PM
    'Brian': (600, 75),        # 10:00 AM - 9:30 PM
    'Laura': (255, 30),        # 4:15 PM - 8:30 PM
    'Sandra': (1110, 60),      # 9:15 AM - 6:30 PM
    'Karen': (1110, 75),       # 6:30 PM - 10:00 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Linda': 30,
    'Kenneth': 30,
    'Kimberly': 30,
    'Paul': 15,
    'Carol': 60,
    'Brian': 75,
    'Laura': 30,
    'Sandra': 60,
    'Karen': 75,
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

# Travel time constraints from Pacific Heights (arrival at 9:00 AM)
travel_times_to_friends = {
    'Linda': travel_times[('Pacific Heights', 'Marina District')],
    'Kenneth': travel_times[('Pacific Heights', 'The Castro')],
    'Kimberly': travel_times[('Pacific Heights', 'Richmond District')],
    'Paul': travel_times[('Pacific Heights', 'Alamo Square')],
    'Carol': travel_times[('Pacific Heights', 'Financial District')],
    'Brian': travel_times[('Pacific Heights', 'Presidio')],
    'Laura': travel_times[('Pacific Heights', 'Mission District')],
    'Sandra': travel_times[('Pacific Heights', 'Nob Hill')],
    'Karen': travel_times[('Pacific Heights', 'Russian Hill')],
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