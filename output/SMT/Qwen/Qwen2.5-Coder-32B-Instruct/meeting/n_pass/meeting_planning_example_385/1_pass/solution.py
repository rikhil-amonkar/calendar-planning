from z3 import *

# Define the locations
locations = ['Nob Hill', 'Presidio', 'North Beach', 'Fisherman\'s Wharf', 'Pacific Heights']

# Define the travel times between locations
travel_times = {
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Fisherman\'s Wharf'): 11,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Pacific Heights'): 11,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Pacific Heights'): 8,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13
}

# Define the constraints for meeting each friend
meetings = {
    'Jeffrey': {'location': 'Presidio', 'start': 8*60, 'end': 10*60, 'min_duration': 105},
    'Steven': {'location': 'North Beach', 'start': 13*60 + 30, 'end': 22*60, 'min_duration': 45},
    'Barbara': {'location': 'Fisherman\'s Wharf', 'start': 18*60, 'end': 21*30, 'min_duration': 30},
    'John': {'location': 'Pacific Heights', 'start': 9*60, 'end': 13*60 + 30, 'min_duration': 15}
}

# Create a solver instance
solver = Solver()

# Define variables for the start time at each location
arrival_times = {loc: Int(f'arrival_{loc}') for loc in locations}

# Initial arrival time at Nob Hill
solver.add(arrival_times['Nob Hill'] == 9*60)

# Constraints for travel times and meeting durations
for loc, arr_time in arrival_times.items():
    if loc != 'Nob Hill':
        # Add constraints for travel times from other locations
        for prev_loc, travel_time in travel_times.items():
            if prev_loc != loc:
                solver.add(arr_time >= arrival_times[prev_loc] + travel_time)
    
    # Add constraints for meeting durations
    for friend, details in meetings.items():
        if details['location'] == loc:
            # Meeting can only start after arriving at the location
            meeting_start = Int(f'meeting_start_{friend}')
            solver.add(meeting_start >= arr_time)
            # Meeting must end before leaving the location
            meeting_end = Int(f'meeting_end_{friend}')
            solver.add(meeting_end <= details['end'])
            # Meeting duration constraint
            solver.add(meeting_end - meeting_start >= details['min_duration'])

# Objective: Minimize total travel time (not explicitly defined here as we are more interested in meeting constraints)
# The solver will try to find a feasible solution that satisfies all constraints

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for loc, arr_time in arrival_times.items():
        print(f"Arrive at {loc} at {model[arr_time] // 60}:{model[arr_time] % 60:02d}")
    for friend, details in meetings.items():
        meeting_start = model[Int(f'meeting_start_{friend}')]
        meeting_end = model[Int(f'meeting_end_{friend}')]
        print(f"Meet {friend} from {meeting_start // 60}:{meeting_start % 60:02d} to {meeting_end // 60}:{meeting_end % 60:02d}")
else:
    print("No solution found")