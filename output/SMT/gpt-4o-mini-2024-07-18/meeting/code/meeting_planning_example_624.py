from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'The Castro'): 26,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Alamo Square'): 20,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Chinatown'): 20,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Russian Hill'): 18,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Russian Hill'): 7,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Chinatown'): 16,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Russian Hill'): 13,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'The Castro'): 22,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Russian Hill'): 4,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'North Beach'): 5,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Carol': (1260, 60),           # 9:30 PM - 10:30 PM
    'Laura': (1110, 60),           # 11:45 AM - 9:30 PM
    'Karen': (435, 75),            # 7:15 AM - 2:00 PM
    'Elizabeth': (735, 75),        # 12:15 PM - 9:30 PM
    'Deborah': (720, 105),         # 12:00 PM - 3:00 PM
    'Jason': (945, 90),            # 2:45 PM - 7:00 PM
    'Steven': (945, 120),          # 2:45 PM - 6:30 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Carol': 60,
    'Laura': 60,
    'Karen': 75,
    'Elizabeth': 75,
    'Deborah': 105,
    'Jason': 90,
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
    solver.add(meeting_start[friend] >= start_time)  # Must be after the start time
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])  # Calculate end time

# Travel constraints from Golden Gate Park (arrival at 9:00 AM)
travel_times_to_friends = {
    'Carol': travel_times[('Golden Gate Park', 'Haight-Ashbury')],
    'Laura': travel_times[('Golden Gate Park', 'Fisherman\'s Wharf')],
    'Karen': travel_times[('Golden Gate Park', 'The Castro')],
    'Elizabeth': travel_times[('Golden Gate Park', 'Chinatown')],
    'Deborah': travel_times[('Golden Gate Park', 'Alamo Square')],
    'Jason': travel_times[('Golden Gate Park', 'North Beach')],
    'Steven': travel_times[('Golden Gate Park', 'Russian Hill')],
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