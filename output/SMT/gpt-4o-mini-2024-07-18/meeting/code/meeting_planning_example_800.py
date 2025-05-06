from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'The Castro'): 23,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Mission District'): 18,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Mission District'): 20,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Fisherman\'s Wharf'): 10,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Alamo Square'): 21,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Embarcadero'): 19,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Mission District'): 11,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Melissa': (1230, 30),        # 8:15 PM - 9:15 PM
    'Kimberly': (420, 15),        # 7:00 AM - 10:30 AM
    'Joseph': (870, 75),           # 3:30 PM - 7:30 PM
    'Barbara': (1260, 15),         # 8:45 PM - 9:45 PM
    'Kenneth': (735, 105),         # 12:15 PM - 5:15 PM
    'Joshua': (270, 105),          # 4:30 PM - 6:15 PM
    'Brian': (570, 45),            # 9:30 AM - 3:30 PM
    'Steven': (1110, 90),          # 7:30 PM - 9:00 PM
    'Betty': (900, 90),            # 7:00 PM - 8:30 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Melissa': 30,
    'Kimberly': 15,
    'Joseph': 75,
    'Barbara': 15,
    'Kenneth': 105,
    'Joshua': 105,
    'Brian': 45,
    'Steven': 90,
    'Betty': 90,
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

# Travel time constraints from Union Square (arrival at 9:00 AM)
travel_times_to_friends = {
    'Melissa': travel_times[('Union Square', 'The Castro')],
    'Kimberly': travel_times[('Union Square', 'North Beach')],
    'Joseph': travel_times[('Union Square', 'Embarcadero')],
    'Barbara': travel_times[('Union Square', 'Alamo Square')],
    'Kenneth': travel_times[('Union Square', 'Nob Hill')],
    'Joshua': travel_times[('Union Square', 'Presidio')],
    'Brian': travel_times[('Union Square', 'Fisherman\'s Wharf')],
    'Steven': travel_times[('Union Square', 'Mission District')],
    'Betty': travel_times[('Union Square', 'Haight-Ashbury')],
}

# Add constraints for ensuring enough time to meet each friend after traveling
for friend, travel_time in travel_times_to_friends.items():
    solver.add(meeting_start[friend] >= 540 + travel_time)  # 540 = 9:00 AM in minutes

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