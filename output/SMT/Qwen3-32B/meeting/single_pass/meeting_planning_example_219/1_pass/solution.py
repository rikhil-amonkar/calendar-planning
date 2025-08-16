from itertools import permutations, combinations
from z3 import Solver, Int, sat
import json

# Define the friends
friends = [
    {
        'name': 'Emily',
        'location': 1,  # Alamo Square
        'available_start': 705,  # 11:45 AM
        'available_end': 915,    # 3:15 PM
        'duration': 105
    },
    {
        'name': 'Barbara',
        'location': 2,  # Union Square
        'available_start': 1005, # 4:45 PM
        'available_end': 1065,   # 6:15 PM
        'duration': 60
    },
    {
        'name': 'William',
        'location': 3,  # Chinatown
        'available_start': 1035, # 5:15 PM
        'available_end': 1140,   # 7:00 PM
        'duration': 105
    }
]

# Travel time matrix (from Castro, Alamo Square, Union Square, Chinatown)
travel_time = [
    [0, 8, 19, 20],   # Castro
    [8, 0, 14, 16],   # Alamo Square
    [19, 15, 0, 7],   # Union Square
    [22, 17, 7, 0]    # Chinatown
]

# Try subsets from largest to smallest
for subset_size in [3, 2, 1]:
    for subset in combinations(friends, subset_size):
        for perm in permutations(subset):
            solver = Solver()
            starts = []
            ends = []
            current_location = 0  # Start at Castro
            current_time = 540    # 9:00 AM in minutes
            valid = True
            for i, friend in enumerate(perm):
                # Define variables for start and end time of this friend
                start = Int(f"start_{i}")
                end = Int(f"end_{i}")
                starts.append(start)
                ends.append(end)
                # Calculate arrival time at this friend's location
                travel = travel_time[current_location][friend['location']]
                arrival_time = current_time + travel
                # Add constraints
                solver.add(start >= arrival_time)
                solver.add(start >= friend['available_start'])
                solver.add(start + friend['duration'] <= friend['available_end'])
                solver.add(end == start + friend['duration'])
                # Update current time and location for next friend
                current_time = end
                current_location = friend['location']
            if solver.check() == sat:
                model = solver.model()
                itinerary = []
                for i, friend in enumerate(perm):
                    start_val = model.evaluate(starts[i]).as_long()
                    end_val = model.evaluate(ends[i]).as_long()
                    # Convert to HH:MM format
                    start_hh = start_val // 60
                    start_mm = start_val % 60
                    end_hh = end_val // 60
                    end_mm = end_val % 60
                    start_time = f"{start_hh:02d}:{start_mm:02d}"
                    end_time = f"{end_hh:02d}:{end_mm:02d}"
                    itinerary.append({
                        "action": "meet",
                        "person": friend['name'],
                        "start_time": start_time,
                        "end_time": end_time
                    })
                print(json.dumps({"itinerary": itinerary}))
                exit()

# If no solution found (shouldn't happen here)
print(json.dumps({"itinerary": []}))