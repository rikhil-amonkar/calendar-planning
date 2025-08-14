from z3 import *
from itertools import permutations

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
    'Sarah': (645, 420),  # 10:45 AM to 7:00 PM
    'Richard': (705, 225),  # 11:45 AM to 3:45 PM
    'Elizabeth': (660, 315),  # 11:00 AM to 5:15 PM
    'Michelle': (375, 525)  # 6:15 PM to 8:45 PM
}

# Define the travel constraints
def add_travel_constraints(current_location, next_location, next_start, current_end):
    travel_time = travel_times[(current_location, next_location)]
    solver.add(next_start >= current_end + travel_time)

# Define the meeting constraints
def add_meeting_constraints(friend, start, duration, available):
    solver.add(start >= available[0])
    solver.add(start + duration <= available[1])

# Function to convert minutes to hours and minutes format
def format_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    am_pm = "AM" if hour < 12 else "PM"
    hour = hour % 12 if hour != 0 else 12
    return f"{hour}:{minute:02d} {am_pm}"

# Define the sequence of visits and check all permutations
friends = ['Sarah', 'Richard', 'Elizabeth', 'Michelle']
found_solution = False

for perm in permutations(friends):
    solver = Solver()
    
    # Define the start times for each friend
    sarah_start = Int('sarah_start')
    richard_start = Int('richard_start')
    elizabeth_start = Int('elizabeth_start')
    michelle_start = Int('michelle_start')
    
    # Add constraints for meeting times
    solver.add(sarah_start >= 645)
    solver.add(sarah_start + 30 <= 420)
    
    solver.add(richard_start >= 705)
    solver.add(richard_start + 90 <= 225)
    
    solver.add(elizabeth_start >= 660)
    solver.add(elizabeth_start + 120 <= 315)
    
    solver.add(michelle_start >= 375)
    solver.add(michelle_start + 90 <= 525)
    
    current_end = start_time
    
    for i in range(len(perm)):
        friend = perm[i]
        start_var = None
        if friend == 'Sarah':
            start_var = sarah_start
        elif friend == 'Richard':
            start_var = richard_start
        elif friend == 'Elizabeth':
            start_var = elizabeth_start
        elif friend == 'Michelle':
            start_var = michelle_start
        
        duration = durations[friend]
        available = available_times[friend]
        
        # Add meeting constraints
        add_meeting_constraints(friend, start_var, duration, available)
        
        # Add travel constraints if not the first visit
        if i > 0:
            prev_friend = perm[i - 1]
            prev_end = None
            if prev_friend == 'Sarah':
                prev_end = sarah_start + durations['Sarah']
            elif prev_friend == 'Richard':
                prev_end = richard_start + durations['Richard']
            elif prev_friend == 'Elizabeth':
                prev_end = elizabeth_start + durations['Elizabeth']
            elif prev_friend == 'Michelle':
                prev_end = michelle_start + durations['Michelle']
            
            add_travel_constraints(locations[prev_friend], locations[friend], start_var, prev_end)
        
        # Update the current end time
        current_end = start_var + duration
    
    # Check if the constraints are satisfiable
    if solver.check() == sat:
        model = solver.model()
        solution = {
            'Sarah': model[sarah_start].as_long(),
            'Richard': model[richard_start].as_long(),
            'Elizabeth': model[elizabeth_start].as_long(),
            'Michelle': model[michelle_start].as_long(),
        }
        print("SOLUTION:")
        for friend, start_time in solution.items():
            print(f"Meet {friend} at {format_time(start_time)}")
        found_solution = True
        break

if not found_solution:
    print("No feasible schedule found.")