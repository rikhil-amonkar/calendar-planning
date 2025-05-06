from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Mission District'): 15,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Mission District'): 17,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Mission District'): 7,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'The Castro'): 19,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Mission District'): 13,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Mission District'): 20,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Mission District'): 14,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Mission District'): 25,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Mission District'): 10,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Mission District'): 17,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Bayview'): 14,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Financial District'): 15,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Helen': (570, 45),         # 9:30 AM - 12:15 PM
    'Steven': (1215, 105),      # 8:15 PM - 10:00 PM
    'Deborah': (510, 30),       # 8:30 AM - 12:00 PM
    'Matthew': (555, 45),       # 9:15 AM - 2:15 PM
    'Joseph': (135, 120),       # 2:15 PM - 6:45 PM
    'Ronald': (960, 60),        # 4:00 PM - 8:45 PM
    'Robert': (1110, 120),      # 6:30 PM - 9:15 PM
    'Rebecca': (885, 30),       # 2:45 PM - 4:15 PM
    'Elizabeth': (1110, 120),   # 6:30 PM - 9:00 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Helen': 45,
    'Steven': 105,
    'Deborah': 30,
    'Matthew': 45,
    'Joseph': 120,
    'Ronald': 60,
    'Robert': 120,
    'Rebecca': 30,
    'Elizabeth': 120,
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting times based on friends' availability
for friend in meeting_times.keys():
    start_time, _ = meeting_times[friend]
    solver.add(meeting_start[friend] >= start_time)  # Must be after their start time
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])  # Calculate end time

# Travel constraints from Pacific Heights (arrival at 9:00 AM)
travel_times_to_friends = {
    'Helen': travel_times[('Pacific Heights', 'Golden Gate Park')],
    'Steven': travel_times[('Pacific Heights', 'The Castro')],
    'Deborah': travel_times[('Pacific Heights', 'Bayview')],
    'Matthew': travel_times[('Pacific Heights', 'Marina District')],
    'Joseph': travel_times[('Pacific Heights', 'Union Square')],
    'Ronald': travel_times[('Pacific Heights', 'Sunset District')],
    'Robert': travel_times[('Pacific Heights', 'Alamo Square')],
    'Rebecca': travel_times[('Pacific Heights', 'Financial District')],
    'Elizabeth': travel_times[('Pacific Heights', 'Mission District')],
}

# Add constraints for ensuring enough time to meet each friend after travel
for friend, travel_time in travel_times_to_friends.items():
    solver.add(meeting_start[friend] >= meeting_times['Helen'][0] + travel_time)  # Must start after travel time + their start time

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