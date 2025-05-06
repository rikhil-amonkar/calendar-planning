from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Sunset District'): 30,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Sunset District'): 15,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Presidio'): 32,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'The Castro'): 19,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'Sunset District'): 23,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Sunset District'): 23,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Sunset District'): 17,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Sunset District'): 19,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Bayview'): 27,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Sunset District'): 11,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Sunset District'): 27,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Union Square'): 30,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Mark': (495, 30),            # 8:15 AM - 10:00 AM
    'Stephanie': (735, 75),       # 12:15 PM - 3:00 PM
    'Betty': (435, 15),           # 7:15 AM - 8:30 PM
    'Lisa': (990, 45),            # 3:30 PM - 6:30 PM
    'William': (945, 60),         # 6:45 PM - 8:00 PM
    'Brian': (555, 30),           # 9:15 AM - 1:15 PM
    'Joseph': (645, 90),          # 10:45 AM - 3:00 PM
    'Ashley': (585, 45),          # 9:45 AM - 11:15 AM
    'Patricia': (1050, 120),      # 4:30 PM - 8:00 PM
    'Karen': (1050, 105),         # 4:30 PM - 10:00 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Mark': 30,
    'Stephanie': 75,
    'Betty': 15,
    'Lisa': 45,
    'William': 60,
    'Brian': 30,
    'Joseph': 90,
    'Ashley': 45,
    'Patricia': 120,
    'Karen': 105,
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

# Travel time constraints from Financial District (arrival at 9:00 AM)
travel_times_to_friends = {
    'Mark': travel_times[('Financial District', 'Fisherman\'s Wharf')],
    'Stephanie': travel_times[('Financial District', 'Presidio')],
    'Betty': travel_times[('Financial District', 'Bayview')],
    'Lisa': travel_times[('Financial District', 'Haight-Ashbury')],
    'William': travel_times[('Financial District', 'Russian Hill')],
    'Brian': travel_times[('Financial District', 'The Castro')],
    'Joseph': travel_times[('Financial District', 'Marina District')],
    'Ashley': travel_times[('Financial District', 'Richmond District')],
    'Patricia': travel_times[('Financial District', 'Union Square')],
    'Karen': travel_times[('Financial District', 'Sunset District')],
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