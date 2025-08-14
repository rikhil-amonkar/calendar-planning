from z3 import *

# Define the locations
locations = ['The Castro', 'Alamo Square', 'Union Square', 'Chinatown']

# Define the travel times in minutes
travel_times = {
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Chinatown'): 20,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Chinatown'): 16,
    ('Union Square', 'The Castro'): 19,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Union Square'): 7,
}

# Define the friends' availability and meeting durations
friends_info = {
    'Emily': {'location': 'Alamo Square', 'start': 11*60 + 45, 'end': 15*60 + 15, 'duration': 105},
    'Barbara': {'location': 'Union Square', 'start': 16*60 + 45, 'end': 18*60 + 15, 'duration': 60},
    'William': {'location': 'Chinatown', 'start': 17*60 + 15, 'end': 19*60, 'duration': 105},
}

# Create a solver instance
solver = Solver()

# Define variables for the arrival time at each location
arrival_times = {loc: Int(f'arrival_{loc}') for loc in locations}

# Set the initial arrival time at The Castro
solver.add(arrival_times['The Castro'] == 9*60)  # 9:00 AM

# Define variables for the meeting times with each friend
meeting_times = {friend: Bool(f'meeting_{friend}') for friend in friends_info}

# Add constraints for meeting each friend
for friend, info in friends_info.items():
    loc = info['location']
    start = info['start']
    end = info['end']
    duration = info['duration']
    
    # Constraint to meet the friend if we arrive at their location within their availability
    solver.add(Implies(meeting_times[friend], And(
        arrival_times[loc] <= start,
        arrival_times[loc] + duration <= end
    )))

# Add constraints for travel times between locations
for i, loc1 in enumerate(locations):
    for loc2 in locations[i+1:]:
        travel_time = travel_times[(loc1, loc2)]
        solver.add(arrival_times[loc2] >= arrival_times[loc1] + travel_time)
        solver.add(arrival_times[loc1] >= arrival_times[loc2] + travel_time)

# Constraint to meet exactly 2 people
solver.add(Sum([If(meeting_times[friend], 1, 0) for friend in friends_info]) == 2)

# Check if the problem is solvable and print the solution
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for friend, info in friends_info.items():
        loc = info['location']
        if model.evaluate(meeting_times[friend]):
            arrival = model.evaluate(arrival_times[loc]).as_long()
            print(f"Meet {friend} at {loc} from {arrival//60}:{arrival%60:02d} to {(arrival + info['duration'])//60}:{(arrival + info['duration'])%60:02d}")
else:
    print("No solution found.")