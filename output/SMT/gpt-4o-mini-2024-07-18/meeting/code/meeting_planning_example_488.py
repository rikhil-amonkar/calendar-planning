from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Sunset District'): 25,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Sunset District'): 15,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Ronald': (600, 105),    # 10:00 AM - 5:00 PM
    'Sarah': (435, 45),      # 7:15 AM - 9:30 AM
    'Helen': (780, 120),      # 1:30 PM - 5:00 PM
    'Joshua': (855, 90),      # 2:15 PM - 7:30 PM
    'Margaret': (615, 60),    # 10:15 AM - 10:00 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Ronald': 105,
    'Sarah': 45,
    'Helen': 120,
    'Joshua': 90,
    'Margaret': 60,
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

# Travel constraints from Pacific Heights (arrival at 9:00 AM)
travel_times_to_friends = {
    'Ronald': travel_times[('Pacific Heights', 'Nob Hill')],
    'Sarah': travel_times[('Pacific Heights', 'Russian Hill')],
    'Helen': travel_times[('Pacific Heights', 'The Castro')],
    'Joshua': travel_times[('Pacific Heights', 'Sunset District')],
    'Margaret': travel_times[('Pacific Heights', 'Haight-Ashbury')],
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