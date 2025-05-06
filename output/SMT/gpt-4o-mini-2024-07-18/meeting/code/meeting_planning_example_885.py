from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Nob Hill'): 12,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Nob Hill'): 8,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Nob Hill'): 16,
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'The Castro'): 19,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Nob Hill'): 20,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Nob Hill'): 27,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Bayview'): 19,
    ('Nob Hill', 'Sunset District'): 24,
    ('Nob Hill', 'Haight-Ashbury'): 13,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Mark': (1110, 90),         # 6:45 PM - 9:00 PM
    'Karen': (765, 90),         # 9:30 AM - 12:45 PM
    'Barbara': (600, 90),       # 10:00 AM - 7:30 PM
    'Nancy': (1080, 105),       # 4:45 PM - 8:00 PM
    'David': (540, 120),        # 9:00 AM - 6:00 PM
    'Linda': (930, 45),         # 6:15 PM - 7:45 PM
    'Kevin': (600, 120),        # 10:00 AM - 5:45 PM
    'Matthew': (615, 45),       # 10:15 AM - 3:30 PM
    'Andrew': (705, 105),       # 11:45 AM - 4:45 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Mark': 90,
    'Karen': 90,
    'Barbara': 90,
    'Nancy': 105,
    'David': 120,
    'Linda': 45,
    'Kevin': 120,
    'Matthew': 45,
    'Andrew': 105,
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

# Travel time constraints from Russian Hill (arrival at 9:00 AM)
travel_times_to_friends = {
    'Mark': travel_times[('Russian Hill', 'Marina District')],
    'Karen': travel_times[('Russian Hill', 'Financial District')],
    'Barbara': travel_times[('Russian Hill', 'Alamo Square')],
    'Nancy': travel_times[('Russian Hill', 'Golden Gate Park')],
    'David': travel_times[('Russian Hill', 'The Castro')],
    'Linda': travel_times[('Russian Hill', 'Bayview')],
    'Kevin': travel_times[('Russian Hill', 'Sunset District')],
    'Matthew': travel_times[('Russian Hill', 'Haight-Ashbury')],
    'Andrew': travel_times[('Russian Hill', 'Nob Hill')],
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