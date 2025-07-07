from z3 import *

# Define the locations
locations = ['Nob Hill', 'North Beach', 'Fisherman\'s Wharf', 'Bayview']

# Define the travel times between locations (in minutes)
travel_times = {
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Fisherman\'s Wharf'): 11,
    ('Nob Hill', 'Bayview'): 19,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Bayview'): 22,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Bayview', 'Nob Hill'): 20,
    ('Bayview', 'North Beach'): 21,
    ('Bayview', 'Fisherman\'s Wharf'): 25
}

# Define the friends' availability and meeting requirements
friends_info = {
    'Helen': {'location': 'North Beach', 'start': 7*60, 'end': 16*60 + 45, 'min_meeting_time': 120},
    'Kimberly': {'location': 'Fisherman\'s Wharf', 'start': 16*60 + 30, 'end': 21*60, 'min_meeting_time': 45},
    'Patricia': {'location': 'Bayview', 'start': 18*60, 'end': 21*60 + 15, 'min_meeting_time': 120}
}

# Create a solver instance
solver = Solver()

# Define variables for the time spent at each location
time_at_location = {friend: Int(f"time_at_{friend}") for friend in friends_info}

# Define variables for the arrival time at each location
arrival_time = {location: Int(f"arrival_at_{location}") for location in locations}

# Set the initial arrival time at Nob Hill
solver.add(arrival_time['Nob Hill'] == 9*60)

# Constraints for meeting each friend
for friend, info in friends_info.items():
    loc = info['location']
    start = info['start']
    end = info['end']
    min_meeting_time = info['min_meeting_time']
    
    # Arrival time at the friend's location must be within their availability
    solver.add(arrival_time[loc] >= start)
    solver.add(arrival_time[loc] <= end - min_meeting_time)
    
    # Time spent meeting the friend must be at least the minimum required
    solver.add(time_at_location[friend] >= min_meeting_time)
    
    # Departure time from the friend's location must be within their availability
    solver.add(arrival_time[loc] + time_at_location[friend] <= end)

# Constraints for traveling between locations
for friend in friends_info:
    loc = friends_info[friend]['location']
    for other_loc in locations:
        if loc != other_loc:
            travel_time = travel_times[(loc, other_loc)]
            # If you meet friend at loc, you must leave loc before arriving at other_loc
            solver.add(arrival_time[loc] + time_at_location[friend] + travel_time <= arrival_time[other_loc])

# Ensure we meet exactly 3 friends
solver.add(Sum([If(time_at_location[friend] > 0, 1, 0) for friend in friends_info]) == 3)

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = {str(d): model[d].as_long() for d in model.decls()}
    print("SOLUTION:")
    for loc in locations:
        print(f"Arrival at {loc}: {solution[f'arrival_at_{loc}']} minutes past midnight")
    for friend in friends_info:
        print(f"Time spent with {friend}: {solution[f'time_at_{friend}']} minutes")
else:
    print("No solution found")