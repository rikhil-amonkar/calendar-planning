from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Bayview', 'North Beach'): 22,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Nob Hill'): 20,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Presidio'): 32,
    ('Bayview', 'Chinatown'): 19,
    ('Bayview', 'Pacific Heights'): 23,
    ('North Beach', 'Bayview'): 25,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Pacific Heights'): 8,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Alamo Square'): 21,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Nob Hill', 'Bayview'): 19,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Fisherman\'s Wharf'): 10,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Pacific Heights'): 15,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Chinatown'): 15,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Pacific Heights'): 11,
    ('Chinatown', 'Bayview'): 20,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Chinatown'): 11,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Brian': (780, 90),          # 1:00 PM - 7:00 PM
    'Richard': (660, 60),        # 11:00 AM - 12:45 PM
    'Ashley': (900, 90),         # 3:00 PM - 8:30 PM
    'Elizabeth': (705, 75),      # 11:45 AM - 6:30 PM
    'Jessica': (1200, 105),      # 8:00 PM - 9:45 PM
    'Deborah': (930, 60),        # 5:30 PM - 10:00 PM
    'Kimberly': (930, 45),       # 5:30 PM - 9:15 PM
    'Matthew': (495, 15),        # 8:15 AM - 9:00 AM
    'Kenneth': (1050, 105),      # 1:45 PM - 7:30 PM
    'Anthony': (855, 30),        # 2:15 PM - 4:00 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Brian': 90,
    'Richard': 60,
    'Ashley': 90,
    'Elizabeth': 75,
    'Jessica': 105,
    'Deborah': 60,
    'Kimberly': 45,
    'Matthew': 15,
    'Kenneth': 105,
    'Anthony': 30,
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

# Travel time constraints from Bayview (arrival at 9:00 AM)
travel_times_to_friends = {
    'Brian': travel_times[('Bayview', 'North Beach')],
    'Richard': travel_times[('Bayview', 'Fisherman\'s Wharf')],
    'Ashley': travel_times[('Bayview', 'Haight-Ashbury')],
    'Elizabeth': travel_times[('Bayview', 'Nob Hill')],
    'Jessica': travel_times[('Bayview', 'Golden Gate Park')],
    'Deborah': travel_times[('Bayview', 'Union Square')],
    'Kimberly': travel_times[('Bayview', 'Alamo Square')],
    'Matthew': travel_times[('Bayview', 'Presidio')],
    'Kenneth': travel_times[('Bayview', 'Chinatown')],
    'Anthony': travel_times[('Bayview', 'Pacific Heights')],
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