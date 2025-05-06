from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'North Beach'): 7,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'North Beach'): 3,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'North Beach'): 10,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'North Beach'): 9,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Pacific Heights'): 8,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Stephanie': (660, 105),        # 11:00 AM - 3:00 PM
    'Karen': (105, 15),             # 1:45 PM - 4:30 PM
    'Brian': (180, 30),             # 3:00 PM - 5:15 PM
    'Rebecca': (495, 30),           # 8:00 AM - 11:15 AM
    'Joseph': (510, 60),            # 8:15 AM - 9:30 AM
    'Steven': (150, 120),           # 2:30 PM - 8:45 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Stephanie': 105,
    'Karen': 15,
    'Brian': 30,
    'Rebecca': 30,
    'Joseph': 60,
    'Steven': 120,
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

# Travel constraints from Financial District (arrival at 9:00 AM)
travel_times_to_friends = {
    'Stephanie': travel_times[('Financial District', 'Golden Gate Park')],
    'Karen': travel_times[('Financial District', 'Chinatown')],
    'Brian': travel_times[('Financial District', 'Union Square')],
    'Rebecca': travel_times[('Financial District', 'Fisherman\'s Wharf')],
    'Joseph': travel_times[('Financial District', 'Pacific Heights')],
    'Steven': travel_times[('Financial District', 'North Beach')],
}

# Add constraints for ensuring enough time to meet each friend after travel time
for friend, travel_time in travel_times_to_friends.items():
    solver.add(meeting_start[friend] >= 540 + travel_time)  # Must start after travel time (540 = 9:00 AM in minutes)

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