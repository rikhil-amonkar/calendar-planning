import z3
from itertools import permutations, combinations
import json

# Define friends with their constraints
friends = [
    {
        'name': 'Jessica',
        'location': 'Golden Gate Park',
        'available_start': 13 * 60 + 45,  # 1:45 PM
        'available_end': 15 * 60,         # 3:00 PM
        'min_duration': 30
    },
    {
        'name': 'Ashley',
        'location': 'Bayview',
        'available_start': 17 * 60 + 15,  # 5:15 PM
        'available_end': 20 * 60,         # 8:00 PM
        'min_duration': 105
    },
    {
        'name': 'Ronald',
        'location': 'Chinatown',
        'available_start': 7 * 60 + 15,   # 7:15 AM
        'available_end': 14 * 60 + 45,    # 2:45 PM
        'min_duration': 90
    },
    {
        'name': 'William',
        'location': 'North Beach',
        'available_start': 13 * 60 + 15,  # 1:15 PM
        'available_end': 20 * 60 + 15,    # 8:15 PM
        'min_duration': 15
    },
    {
        'name': 'Daniel',
        'location': 'Mission District',
        'available_start': 7 * 60,        # 7:00 AM
        'available_end': 11 * 60 + 15,    # 11:15 AM
        'min_duration': 105
    }
]

# Define travel times between locations
travel_times = {
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Mission District'): 26,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Bayview', 'Presidio'): 31,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Chinatown'): 18,
    ('Bayview', 'North Beach'): 21,
    ('Bayview', 'Mission District'): 13,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Bayview'): 22,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Mission District'): 18,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Bayview'): 22,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Mission District'): 18,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'North Beach'): 17,
}

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Starting time at Presidio (9:00 AM)
start_time_presidio = 9 * 60  # 540 minutes

# Try subsets from largest to smallest
for subset_size in range(len(friends), 0, -1):
    for subset in combinations(friends, subset_size):
        # Generate all permutations of the subset
        for perm in permutations(subset):
            # Create Z3 solver
            solver = z3.Solver()
            # Create variables for start times
            starts = [z3.Int(f'start_{i}') for i in range(len(perm))]
            # Add constraints
            for i in range(len(perm)):
                friend = perm[i]
                # Start time must be >= available_start
                solver.add(starts[i] >= friend['available_start'])
                # End time must be <= available_end
                end_time = starts[i] + friend['min_duration']
                solver.add(end_time <= friend['available_end'])
                # For the first meeting, add arrival time constraint
                if i == 0:
                    # Travel from Presidio to friend's location
                    travel_time = travel_times[('Presidio', friend['location'])]
                    solver.add(starts[i] >= start_time_presidio + travel_time)
                # For consecutive meetings, add travel time constraints
                if i > 0:
                    prev_friend = perm[i-1]
                    current_friend = friend
                    travel_time = travel_times[(prev_friend['location'], current_friend['location'])]
                    prev_end = starts[i-1] + prev_friend['min_duration']
                    solver.add(starts[i] >= prev_end + travel_time)
            # Check if the constraints are satisfiable
            if solver.check() == z3.sat:
                model = solver.model()
                # Generate itinerary
                itinerary = []
                for i in range(len(perm)):
                    friend = perm[i]
                    start_val = model[starts[i]].as_long()
                    end_val = start_val + friend['min_duration']
                    itinerary.append({
                        'action': 'meet',
                        'location': friend['location'],
                        'person': friend['name'],
                        'start_time': minutes_to_time_str(start_val),
                        'end_time': minutes_to_time_str(end_val)
                    })
                # Output the JSON
                print(json.dumps({"itinerary": itinerary}, indent=2))
                exit()  # Exit after finding the first valid solution

# If no solution found (unlikely given the problem)
print(json.dumps({"itinerary": []}))