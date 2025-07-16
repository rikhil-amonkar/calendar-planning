from z3 import *

# Define the time slots in minutes from 9:00AM to 10:30PM (750 minutes)
time_slots = list(range(0, 751))

# Define the duration of each meeting
duration_sarah = 105
duration_mary = 75
duration_helen = 30
duration_thomas = 120

# Define the available time slots for each friend
available_sarah = lambda start: And(start >= 285, start + duration_sarah <= 570)  # 2:45PM to 5:30PM
available_mary = lambda start: And(start >= 60, start + duration_mary <= 435)     # 1:00PM to 7:15PM
available_helen = lambda start: And(start >= 645, start + duration_helen <= 660)  # 9:45PM to 10:30PM
available_thomas = lambda start: And(start >= 195, start + duration_thomas <= 405) # 3:15PM to 6:45PM

# Define travel times in minutes
travel_times = {
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Bayview'): 26,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Bayview'): 15,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Mission District'): 13,
}

# Define the current location and the start time
current_location = 'Haight-Ashbury'
start_time = 0

# Define a function to add travel constraints
def add_travel_constraint(solver, prev_location, next_location, prev_end_time, next_start_time):
    travel_time = travel_times[(prev_location, next_location)]
    solver.add(next_start_time >= prev_end_time + travel_time)

# Define a function to check a specific combination of friends
def check_combination(friends):
    solver = Solver()
    
    # Define variables for the start time of each meeting
    start_vars = {friend: Int(f'start_{friend}') for friend in friends}
    
    # Add constraints for available time slots
    for friend, start in start_vars.items():
        if friend == 'Sarah':
            solver.add(available_sarah(start))
        elif friend == 'Mary':
            solver.add(available_mary(start))
        elif friend == 'Helen':
            solver.add(available_helen(start))
        elif friend == 'Thomas':
            solver.add(available_thomas(start))
    
    # Sort friends by their earliest available start time
    friends_sorted = sorted(friends, key=lambda friend: start_vars[friend].as_ast())
    
    # Add travel constraints
    prev_location = current_location
    prev_end_time = start_time
    for friend in friends_sorted:
        start = start_vars[friend]
        location = {
            'Sarah': 'Fisherman\'s Wharf',
            'Mary': 'Richmond District',
            'Helen': 'Mission District',
            'Thomas': 'Bayview'
        }[friend]
        add_travel_constraint(solver, prev_location, location, prev_end_time, start)
        prev_location = location
        prev_end_time = start + {'Sarah': duration_sarah, 'Mary': duration_mary, 'Helen': duration_helen, 'Thomas': duration_thomas}[friend]
    
    # Check if the solution is feasible
    if solver.check() == sat:
        model = solver.model()
        print("SOLUTION:")
        for friend in friends_sorted:
            start = model[start_vars[friend]]
            end = start + {'Sarah': duration_sarah, 'Mary': duration_mary, 'Helen': duration_helen, 'Thomas': duration_thomas}[friend]
            location = {
                'Sarah': 'Fisherman\'s Wharf',
                'Mary': 'Richmond District',
                'Helen': 'Mission District',
                'Thomas': 'Bayview'
            }[friend]
            print(f"Meet {friend} at {location} from {start} to {end}")
        return True
    return False

# List of all friends
friends = ['Sarah', 'Mary', 'Helen', 'Thomas']

# Check all combinations of 3 friends
from itertools import combinations

for combo in combinations(friends, 3):
    if check_combination(combo):
        break
else:
    print("No solution found")