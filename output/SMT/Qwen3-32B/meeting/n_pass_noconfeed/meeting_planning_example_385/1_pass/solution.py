import itertools
from z3 import *
import json

# Define friends and their constraints
friends = [
    {
        'name': 'Jeffrey',
        'location': 'Presidio',
        'available_start': 8 * 60,  # 8:00 AM
        'available_end': 10 * 60,   # 10:00 AM
        'required_duration': 105
    },
    {
        'name': 'Steven',
        'location': 'North Beach',
        'available_start': 13 * 60 + 30,  # 1:30 PM
        'available_end': 22 * 60,         # 10:00 PM
        'required_duration': 45
    },
    {
        'name': 'Barbara',
        'location': "Fisherman's Wharf",
        'available_start': 18 * 60,       # 6:00 PM
        'available_end': 21 * 60 + 30,    # 9:30 PM
        'required_duration': 30
    },
    {
        'name': 'John',
        'location': 'Pacific Heights',
        'available_start': 9 * 60,        # 9:00 AM
        'available_end': 13 * 60 + 30,    # 1:30 PM
        'required_duration': 15
    }
]

# Define travel times between locations (in minutes)
travel_times = {
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', "Fisherman's Wharf"): 11,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', "Fisherman's Wharf"): 19,
    ('Presidio', 'Pacific Heights'): 11,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', "Fisherman's Wharf"): 5,
    ('North Beach', 'Pacific Heights'): 8,
    ("Fisherman's Wharf", 'Nob Hill'): 11,
    ("Fisherman's Wharf", 'Presidio'): 17,
    ("Fisherman's Wharf", 'North Beach'): 6,
    ("Fisherman's Wharf", 'Pacific Heights'): 13,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', "Fisherman's Wharf"): 13,
}

# Arrival time at Nob Hill in minutes since midnight
arrival_time = 9 * 60  # 9:00 AM

# Check all subsets of friends in descending order of size
for subset_size in range(len(friends), 0, -1):
    for subset in itertools.combinations(friends, subset_size):
        # Check all permutations of the subset
        for perm in itertools.permutations(subset):
            solver = Solver()
            start_times = [Int(f"start_{i}") for i in range(len(perm))]
            
            prev_loc = 'Nob Hill'
            prev_end = arrival_time
            
            for i, friend in enumerate(perm):
                current_loc = friend['location']
                travel_time = travel_times[(prev_loc, current_loc)]
                
                # Start time must be after previous end + travel time
                solver.add(start_times[i] >= prev_end + travel_time)
                
                # Start time must be within available window
                solver.add(start_times[i] >= friend['available_start'])
                
                # End time must be within available window
                end_time = start_times[i] + friend['required_duration']
                solver.add(end_time <= friend['available_end'])
                
                # Update for next iteration
                prev_end = end_time
                prev_loc = current_loc
            
            if solver.check() == sat:
                model = solver.model()
                itinerary = []
                for i, friend in enumerate(perm):
                    start = model[start_times[i]].as_long()
                    duration = friend['required_duration']
                    end = start + duration
                    
                    # Convert start and end times to H:MM format
                    start_h = start // 60
                    start_m = start % 60
                    end_h = end // 60
                    end_m = end % 60
                    
                    start_str = f"{start_h}:{start_m:02d}"
                    end_str = f"{end_h}:{end_m:02d}"
                    
                    itinerary.append({
                        "action": "meet",
                        "location": friend['location'],
                        "person": friend['name'],
                        "start_time": start_str,
                        "end_time": end_str
                    })
                
                # Output the result as JSON
                print(json.dumps({"itinerary": itinerary}, indent=2))
                exit()

# If no solution is found (unlikely given the problem constraints)
print(json.dumps({"itinerary": []}))