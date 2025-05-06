from z3 import *

# Define places
places = ['Haight', 'Fisherman', 'Richmond', 'Mission', 'Bayview']

# Define travel times (in minutes)
travel_times = {
    ('Haight', 'Fisherman'): 23,
    ('Haight', 'Richmond'): 10,
    ('Haight', 'Mission'): 11,
    ('Haight', 'Bayview'): 18,
    ('Fisherman', 'Haight'): 22,
    ('Fisherman', 'Richmond'): 18,
    ('Fisherman', 'Mission'): 22,
    ('Fisherman', 'Bayview'): 26,
    ('Richmond', 'Haight'): 10,
    ('Richmond', 'Fisherman'): 18,
    ('Richmond', 'Mission'): 20,
    ('Richmond', 'Bayview'): 26,
    ('Mission', 'Haight'): 12,
    ('Mission', 'Fisherman'): 22,
    ('Mission', 'Richmond'): 20,
    ('Mission', 'Bayview'): 15,
    ('Bayview', 'Haight'): 19,
    ('Bayview', 'Fisherman'): 25,
    ('Bayview', 'Richmond'): 25,
    ('Bayview', 'Mission'): 13,
}

# Meeting times for friends (in minutes after 9:00 AM)
meeting_times = {
    'Sarah': (165, 330),  # 2:45 PM - 5:30 PM
    'Mary': (75, 435),     # 1:00 PM - 7:15 PM
    'Helen': (105, 150),   # 9:45 PM - 10:30 PM
    'Thomas': (195, 405),  # 3:15 PM - 6:45 PM
}

# Minimum meeting durations (in minutes)
meeting_durations = {
    'Sarah': 105,
    'Mary': 75,
    'Helen': 30,
    'Thomas': 120,
}

# Initialize the Z3 solver
solver = Solver()

# Create time variables for meetings with friends
start_times = {friend: Int(f'{friend}_start') for friend in meeting_times.keys()}
end_times = {friend: Int(f'{friend}_end') for friend in meeting_times.keys()}

# Constraints for meeting start and end times
for friend in meeting_times.keys():
    start, end = meeting_times[friend]
    solver.add(start_times[friend] >= start, start_times[friend] <= end)
    solver.add(end_times[friend] == start_times[friend] + meeting_durations[friend])

# Transport decisions (where to go after leaving Haight)
solves_position_var = {}
for place_from in places:
    for place_to in places:
        if place_from != place_to:
            solves_position_var[(place_from, place_to)] = Int(f'sol_{place_from}_{place_to}')

# Constraints for travel times and ensuring they fit in the day
solver.add(
    [solves_position_var[pair] == travel_times[(pair[0], pair[1])] for pair in travel_times.keys()]
)

# Events: Check if time allows for travel between locations
for friend in meeting_times.keys():
    travel_times_to_friend = {
        'Fisherman': travel_times.get(('Haight', 'Fisherman')),
        'Richmond': travel_times.get(('Haight', 'Richmond'), travel_times.get(('Fisherman', 'Richmond'))),
        'Mission': travel_times.get(('Haight', 'Mission')),
        'Bayview': travel_times.get(('Haight', 'Bayview')),
    }

    # Check if we can travel to meet the friends within the allowed time
    for location in travel_times_to_friend.keys():
        travel_time = travel_times_to_friend[location]
        if travel_time is not None:
            solver.add(start_times[friend] >= (travel_time + 0))  # assuming you left at 9:00 AM

# Optimize meeting times (maximize moments spent with friends)
solver.maximize(Sum(end_times.values()) - Sum(start_times.values()))

# Solving
if solver.check() == sat:
    model = solver.model()
    # Gather and print results
    meeting_times_schedule = {}
    for friend in meeting_times.keys():
        meeting_times_schedule[friend] = (model[start_times[friend]].as_long(), model[end_times[friend]].as_long())
    print("Meeting Schedule:")
    for friend, times in meeting_times_schedule.items():
        print(f"{friend}: Start at {times[0]} minutes, End at {times[1]} minutes")
else:
    print("No valid meeting schedule found.")