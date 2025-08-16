from z3 import *
import itertools
import json

# Define friends and their parameters
friends = [
    {'name': 'Andrew', 'location': 'Golden Gate Park', 'available_start': 765, 'available_end': 1410, 'min_duration': 75},
    {'name': 'Sarah', 'location': 'Pacific Heights', 'available_start': 1035, 'available_end': 1245, 'min_duration': 15},
    {'name': 'Nancy', 'location': 'Presidio', 'available_start': 1050, 'available_end': 1155, 'min_duration': 60},
    {'name': 'Rebecca', 'location': 'Chinatown', 'available_start': 585, 'available_end': 1110, 'min_duration': 90},
    {'name': 'Robert', 'location': 'The Castro', 'available_start': 510, 'available_end': 1035, 'min_duration': 30},
]

# Define travel times between locations
travel_times = {
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'The Castro'): 19,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'The Castro'): 16,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'The Castro'): 21,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'The Castro'): 22,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Chinatown'): 20,
}

def get_travel_time(loc1, loc2):
    return travel_times[(loc1, loc2)]

# Generate all permutations of friends
for perm in itertools.permutations(friends):
    s = Solver()
    n = len(perm)
    starts = [Int(f"start_{i}") for i in range(n)]
    ends = [Int(f"end_{i}") for i in range(n)]
    prev_location = 'Union Square'
    prev_end = 540  # 9:00 AM in minutes since midnight
    constraints = []
    for i in range(n):
        friend = perm[i]
        loc = friend['location']
        travel_time = get_travel_time(prev_location, loc)
        arrival_time = prev_end + travel_time
        # Add constraints for start and end times
        constraints.append(starts[i] >= arrival_time)
        constraints.append(starts[i] >= friend['available_start'])
        constraints.append(ends[i] == starts[i] + friend['min_duration'])
        constraints.append(ends[i] <= friend['available_end'])
        # Update for next iteration
        prev_location = loc
        prev_end = ends[i]
    s.add(constraints)
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(n):
            friend = perm[i]
            start_time = model.evaluate(starts[i]).as_long()
            end_time = model.evaluate(ends[i]).as_long()
            # Convert to HH:MM format
            start_hh = start_time // 60
            start_mm = start_time % 60
            end_hh = end_time // 60
            end_mm = end_time % 60
            start_str = f"{start_hh:02d}:{start_mm:02d}"
            end_str = f"{end_hh:02d}:{end_mm:02d}"
            itinerary.append({
                "action": "meet",
                "person": friend['name'],
                "start_time": start_str,
                "end_time": end_str
            })
        print(json.dumps({"itinerary": itinerary}))
        exit()