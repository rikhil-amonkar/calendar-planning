from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Chinatown', 'Mission District'): 18,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Presidio'): 19,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Presidio'): 25,
    ('Alamo Square', 'Chinatown'): 16,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Presidio'): 18,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Presidio'): 11,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Sunset District'): 26,
    ('Union Square', 'Presidio'): 24,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Presidio'): 16,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Alamo Square'): 18,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Sunset District'): 15,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'David': (1140, 45),         # 8:00 AM - 7:45 PM
    'Kenneth': (840, 120),       # 2:00 PM - 7:45 PM
    'John': (1020, 15),          # 5:00 PM - 8:00 PM
    'Charles': (1260, 60),       # 9:45 PM - 10:45 PM
    'Deborah': (420, 90),        # 7:00 AM - 6:15 PM
    'Karen': (1145, 15),         # 5:45 PM - 9:15 PM
    'Carol': (495, 30),          # 8:15 AM - 9:15 AM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'David': 45,
    'Kenneth': 120,
    'John': 15,
    'Charles': 60,
    'Deborah': 90,
    'Karen': 15,
    'Carol': 30,
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

# Travel time constraints from Chinatown (arrival at 9:00 AM)
travel_times_to_friends = {
    'David': travel_times[('Chinatown', 'Mission District')],
    'Kenneth': travel_times[('Chinatown', 'Alamo Square')],
    'John': travel_times[('Chinatown', 'Pacific Heights')],
    'Charles': travel_times[('Chinatown', 'Union Square')],
    'Deborah': travel_times[('Chinatown', 'Golden Gate Park')],
    'Karen': travel_times[('Chinatown', 'Sunset District')],
    'Carol': travel_times[('Chinatown', 'Presidio')],
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