from z3 import *

# Define the locations
locations = ['Golden Gate Park', 'Alamo Square', 'Presidio', 'Russian Hill']

# Define the travel times between locations
travel_times = {
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Presidio'): 18,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Alamo Square'): 18,
    ('Presidio', 'Russian Hill'): 14,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Presidio'): 14
}

# Define the meeting times and durations
meetings = {
    'Timothy': {'location': 'Alamo Square', 'start': 12*60, 'end': 16*60 + 15, 'min_duration': 105},
    'Mark': {'location': 'Presidio', 'start': 18*60 + 45, 'end': 21*60, 'min_duration': 60},
    'Joseph': {'location': 'Russian Hill', 'start': 16*60 + 45, 'end': 21*60 + 30, 'min_duration': 60}
}

# Create a solver instance
solver = Solver()

# Define variables for the time spent at each location
time_at_location = {loc: Int(f"time_at_{loc}") for loc in locations}

# Define variables for the start time at each location
start_time_at_location = {loc: Int(f"start_time_at_{loc}") for loc in locations}

# Initial location is Golden Gate Park at 9:00 AM (540 minutes)
solver.add(start_time_at_location['Golden Gate Park'] == 540)

# Define the constraints for meeting each friend
for name, details in meetings.items():
    loc = details['location']
    start = details['start']
    end = details['end']
    min_duration = details['min_duration']
    
    # Ensure we arrive at the location before the meeting ends and leave after the meeting starts
    solver.add(start_time_at_location[loc] + time_at_location[loc] >= start)
    solver.add(start_time_at_location[loc] <= end - min_duration)
    
    # Ensure we spend at least the minimum duration at the location
    solver.add(time_at_location[loc] >= min_duration)

# Define the constraints for traveling between locations
for i in range(len(locations)):
    for j in range(i+1, len(locations)):
        loc1, loc2 = locations[i], locations[j]
        travel_time = travel_times[(loc1, loc2)]
        
        # Ensure we have enough time to travel between locations
        solver.add(Implies(time_at_location[loc1] > 0, start_time_at_location[loc2] >= start_time_at_location[loc1] + time_at_location[loc1] + travel_time))
        solver.add(Implies(time_at_location[loc2] > 0, start_time_at_location[loc1] >= start_time_at_location[loc2] + time_at_location[loc2] + travel_time))

# Ensure we visit exactly the locations where Timothy, Mark, and Joseph are available
solver.add(time_at_location['Alamo Square'] > 0)
solver.add(time_at_location['Presidio'] > 0)
solver.add(time_at_location['Russian Hill'] > 0)

# Ensure we do not visit Golden Gate Park after starting the day there
solver.add(time_at_location['Golden Gate Park'] == 0)

# Ensure we visit exactly three locations
visited = {loc: Bool(f"visited_{loc}") for loc in locations}
for loc in locations:
    solver.add(visited[loc] == (time_at_location[loc] > 0))

solver.add(Sum([If(visited[loc], 1, 0) for loc in locations]) == 3)

# Objective: Minimize the total time spent not meeting friends
total_non_meeting_time = Int('total_non_meeting_time')
solver.add(total_non_meeting_time == Sum([start_time_at_location[loc] + time_at_location[loc] for loc in locations]) - Sum([meetings[name]['start'] + meetings[name]['min_duration'] for name in meetings]))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for loc in locations:
        print(f"Start time at {loc}: {model[start_time_at_location[loc]]} minutes (or {model[start_time_at_location[loc]] // 60}:{model[start_time_at_location[loc]] % 60:02d})")
        print(f"Time spent at {loc}: {model[time_at_location[loc]]} minutes")
else:
    print("No solution found")