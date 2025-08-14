from z3 import *

# Define the time variables for each friend
sarah_start = Int('sarah_start')
richard_start = Int('richard_start')
elizabeth_start = Int('elizabeth_start')
michelle_start = Int('michelle_start')

# Define the travel times between districts
travel_times = {
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission District'): 17,
}

# Create a solver instance
solver = Solver()

# Add constraints for meeting times
solver.add(sarah_start >= 645)  # 10:45 AM in minutes
solver.add(sarah_start + 30 <= 420)  # Must finish by 7:00 PM (420 minutes)

solver.add(richard_start >= 705)  # 11:45 AM in minutes
solver.add(richard_start + 90 <= 225)  # Must finish by 3:45 PM (225 minutes)

solver.add(elizabeth_start >= 660)  # 11:00 AM in minutes
solver.add(elizabeth_start + 120 <= 315)  # Must finish by 5:15 PM (315 minutes)

solver.add(michelle_start >= 375)  # 6:15 PM in minutes
solver.add(michelle_start + 90 <= 525)  # Must finish by 8:45 PM (525 minutes)

# Define the current location and start time
current_location = 'Richmond District'
start_time = 540  # 9:00 AM in minutes

# Define the locations for each friend
locations = {
    'Sarah': 'Sunset District',
    'Richard': 'Haight-Ashbury',
    'Elizabeth': 'Mission District',
    'Michelle': 'Golden Gate Park'
}

# Define the durations for each meeting
durations = {
    'Sarah': 30,
    'Richard': 90,
    'Elizabeth': 120,
    'Michelle': 90
}

# Define the available times for each friend
available_times = {
    'Sarah': (645, 420),
    'Richard': (705, 225),
    'Elizabeth': (660, 315),
    'Michelle': (375, 525)
}

# Define the travel constraints
def add_travel_constraints(current_location, next_location, next_start, current_end):
    travel_time = travel_times[(current_location, next_location)]
    solver.add(next_start >= current_end + travel_time)

# Define the meeting constraints
def add_meeting_constraints(friend, start, duration, available):
    solver.add(start >= available[0])
    solver.add(start + duration <= available[1])

# Define the sequence of visits
visits = ['Sarah', 'Richard', 'Elizabeth', 'Michelle']
current_end = start_time

for i in range(len(visits)):
    friend = visits[i]
    start_var = globals()[f'{friend}_start']
    duration = durations[friend]
    available = available_times[friend]
    
    # Add meeting constraints
    add_meeting_constraints(friend, start_var, duration, available)
    
    # Add travel constraints if not the first visit
    if i > 0:
        prev_friend = visits[i - 1]
        prev_end = globals()[f'{prev_friend}_start'] + durations[prev_friend]
        add_travel_constraints(locations[prev_friend], locations[friend], start_var, prev_end)
    
    # Update the current end time
    current_end = start_var + duration

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        friend: model[globals()[f'{friend}_start']].as_long()
        for friend in visits
    }
    print("SOLUTION:")
    for friend, start_time in solution.items():
        hour = start_time // 60
        minute = start_time % 60
        am_pm = "AM" if hour < 12 else "PM"
        hour = hour % 12 if hour != 0 else 12
        print(f"Meet {friend} at {hour}:{minute:02d} {am_pm}")
else:
    print("No feasible schedule found.")