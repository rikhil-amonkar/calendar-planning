from z3 import *

# Define places
places = [
    'Bayview', 'Pacific Heights', 'Mission District', 
    'Haight-Ashbury', 'Financial District'
]

# Define travel times (in minutes)
travel_times = {
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Financial District'): 19,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Financial District'): 13,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Financial District'): 17,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Mission District'): 17,
    ('Financial District', 'Haight-Ashbury'): 19,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Mary': (60, 840),        # 10:00 AM - 7:00 PM -> 60 - 840 minutes
    'Lisa': (1020, 1200),     # 8:30 PM - 10:00 PM -> 1020 - 1200 minutes
    'Betty': (0, 315),        # 7:15 AM - 5:15 PM -> 0 - 315 minutes
    'Charles': (675, 900),    # 11:15 AM - 3:00 PM -> 675 - 900 minutes
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Mary': 45,
    'Lisa': 75,
    'Betty': 90,
    'Charles': 120,
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Constraints for meeting start and end times
for friend in meeting_times.keys():
    start_time, end_time = meeting_times[friend]
    solver.add(meeting_start[friend] >= start_time, meeting_start[friend] <= end_time)
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])

# Travel constraints from Bayview
travel_times_to_friends = {
    'Mary': travel_times[('Bayview', 'Pacific Heights')],
    'Lisa': travel_times[('Bayview', 'Mission District')],  # Travel from Bayview to Mission District
    'Betty': travel_times[('Bayview', 'Haight-Ashbury')],   # Travel from Bayview to Haight-Ashbury
    'Charles': travel_times[('Bayview', 'Financial District')] # Travel from Bayview to Financial District
}

# Add constraints for travel times ensuring you arrive on time to meet
for friend in travel_times_to_friends.keys():
    travel_time = travel_times_to_friends[friend]
    if friend in ['Lisa', 'Betty', 'Charles']:
        solver.add(meeting_start[friend] >= travel_time)  # Starting time must account for travel time
        solver.add(meeting_start[friend] >= 0)  # Ensure no negative start time

# Objective: maximize total meeting time
total_meet_time = Sum([meeting_end[friend] - meeting_start[friend] for friend in meeting_times])
solver.maximize(total_meet_time)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    meeting_times_schedule = {}
    for friend in meeting_times.keys():
        start = model[meeting_start[friend]].as_long()
        end = model[meeting_end[friend]].as_long()
        meeting_times_schedule[friend] = (start, end)
    print("SOLUTION:")
    print("Meeting Schedule:")
    for friend, times in meeting_times_schedule.items():
        print(f"{friend}: Start at {times[0]} minutes after 9:00 AM, End at {times[1]} minutes after 9:00 AM")
else:
    print("SOLUTION: No valid meeting schedule found.")