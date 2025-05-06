from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Financial District'): 19,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Embarcadero'): 19,
    ('Mission District', 'Financial District'): 17,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Mission District'): 20,
    ('Embarcadero', 'Financial District'): 5,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Mission District'): 17,
    ('Financial District', 'Embarcadero'): 4,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Joseph': (540, 90),         # 8:00 AM - 5:30 PM
    'Jeffrey': (1050, 60),       # 5:30 PM - 9:30 PM
    'Kevin': (675, 30),          # 11:15 AM - 3:15 PM
    'David': (525, 30),          # 8:15 AM - 9:00 AM
    'Barbara': (630, 15),        # 10:30 AM - 4:30 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Joseph': 90,
    'Jeffrey': 60,
    'Kevin': 30,
    'David': 30,
    'Barbara': 15,
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

# Travel time constraints from Golden Gate Park (arrival at 9:00 AM)
travel_times_to_friends = {
    'Joseph': travel_times[('Golden Gate Park', 'Fisherman\'s Wharf')],
    'Jeffrey': travel_times[('Golden Gate Park', 'Bayview')],
    'Kevin': travel_times[('Golden Gate Park', 'Mission District')],
    'David': travel_times[('Golden Gate Park', 'Embarcadero')],
    'Barbara': travel_times[('Golden Gate Park', 'Financial District')],
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