from z3 import *

# Define places
places = [
    'Richmond District', 'Marina District', 'Chinatown', 
    'Financial District', 'Bayview', 'Union Square'
]

# Define travel times (in minutes)
travel_times = {
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Chinatown'): 20,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Bayview'): 26,
    ('Richmond District', 'Union Square'): 21,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Chinatown'): 16,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Union Square'): 16,
    ('Chinatown', 'Richmond District'): 20,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Bayview'): 22,
    ('Chinatown', 'Union Square'): 7,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Union Square'): 9,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Marina District'): 25,
    ('Bayview', 'Chinatown'): 18,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Union Square'): 17,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Bayview'): 15,
}

# Define meeting times and durations (in minutes after 9:00 AM, which is 0)
meeting_times = {
    'Kimberly': (75, 285),  # 1:15 PM - 4:45 PM
    'Robert': (75, 495),     # 12:15 PM - 8:15 PM
    'Rebecca': (75, 285),    # 1:15 PM - 4:45 PM
    'Margaret': (30, 90),    # 9:30 AM - 1:30 PM
    'Kenneth': (450, 555),    # 7:30 PM - 9:15 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Kimberly': 15,
    'Robert': 15,
    'Rebecca': 75,
    'Margaret': 30,
    'Kenneth': 75,
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

# Define travel times from Richmond District, where you start
travel_times_to_friends = {
    'Kimberly': travel_times[('Richmond District', 'Marina District')],
    'Robert': travel_times[('Richmond District', 'Chinatown')],
    'Rebecca': travel_times[('Richmond District', 'Financial District')],
    'Margaret': travel_times[('Richmond District', 'Bayview')],
    'Kenneth': travel_times[('Richmond District', 'Union Square')],
}

# Add constraints for travel times ensuring you arrive on time
for friend in travel_times_to_friends.keys():
    travel_time = travel_times_to_friends[friend]
    solver.add(meeting_start[friend] >= travel_time)

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