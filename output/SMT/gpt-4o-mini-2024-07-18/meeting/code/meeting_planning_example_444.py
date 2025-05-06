from z3 import *

# Define places
places = [
    'Financial District', 'Russian Hill', 'Sunset District',
    'North Beach', 'The Castro', 'Golden Gate Park'
]

# Define travel times (in minutes)
travel_times = {
    ('Financial District', 'Russian Hill'): 10,
    ('Financial District', 'Sunset District'): 31,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'The Castro'): 23,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'North Beach'): 29,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'The Castro'): 22,
    ('North Beach', 'Golden Gate Park'): 22,
    ('The Castro', 'Financial District'): 20,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'The Castro'): 13,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Ronald': (105, 315),   # 1:45 PM - 5:15 PM
    'Patricia': (15, 1200), # 9:15 AM - 10:00 PM
    'Laura': (30, 45),      # 12:30 PM - 12:45 PM
    'Emily': (255, 390),    # 4:15 PM - 6:30 PM
    'Mary': (180, 270)      # 3:00 PM - 4:30 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Ronald': 105,
    'Patricia': 60,
    'Laura': 15,
    'Emily': 60,
    'Mary': 60,
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

# Travel constraints from Financial District
travel_times_to_friends = {
    'Ronald': travel_times[('Financial District', 'Russian Hill')],
    'Patricia': travel_times[('Financial District', 'Sunset District')],
    'Laura': travel_times[('Financial District', 'North Beach')],
    'Emily': travel_times[('Financial District', 'The Castro')],
    'Mary': travel_times[('Financial District', 'Golden Gate Park')],
}

# Add constraints for travel times ensuring you arrive on time to meet
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