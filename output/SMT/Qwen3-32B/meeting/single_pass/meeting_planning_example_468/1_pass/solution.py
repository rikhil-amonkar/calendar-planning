import itertools
from z3 import *
import json

# Define friends data with corrected times
friends = {
    'Rebecca': {
        'location': 'Bayview',
        'available_start': 540,  # 9:00 AM
        'available_end': 765,    # 12:45 PM
        'max_start': 765 - 90  # 675
    },
    'Amanda': {
        'location': 'Pacific Heights',
        'available_start': 1110,  # 6:30 PM
        'available_end': 1285,   # 9:45 PM
        'max_start': 1285 - 90  # 1195
    },
    'James': {
        'location': 'Alamo Square',
        'available_start': 585,  # 9:45 AM
        'available_end': 1275,   # 9:15 PM
        'max_start': 1275 - 90  # 1185
    },
    'Sarah': {
        'location': 'Fisherman\'s Wharf',
        'available_start': 480,  # 8:00 AM
        'available_end': 1290,   # 9:30 PM
        'max_start': 1290 - 90  # 1200
    },
    'Melissa': {
        'location': 'Golden Gate Park',
        'available_start': 540,  # 9:00 AM
        'available_end': 1125,   # 6:45 PM
        'max_start': 1125 - 90  # 1035
    }
}

# Define travel times between locations
travel_times = {
    ('Castro', 'Bayview'): 19,
    ('Castro', 'Pacific Heights'): 16,
    ('Castro', 'Alamo Square'): 8,
    ('Castro', 'Fisherman\'s Wharf'): 24,
    ('Castro', 'Golden Gate Park'): 11,
    ('Bayview', 'Castro'): 20,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Pacific Heights', 'Castro'): 16,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Alamo Square', 'Castro'): 8,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Fisherman\'s Wharf', 'Castro'): 26,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Alamo Square'): 20,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Golden Gate Park', 'Castro'): 13,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
}

friends_list = ['Rebecca', 'Amanda', 'James', 'Sarah', 'Melissa']

for k in range(5, 0, -1):
    # Generate all combinations of k friends
    for subset in itertools.combinations(friends_list, k):
        # Generate all permutations of the subset
        for perm in itertools.permutations(subset):
            variables = {name: Int(f'start_{name}') for name in perm}
            constraints = []
            # Initial location is Castro at 540 (9:00 AM)
            current_time = 540
            current_loc = 'Castro'
            for i, name in enumerate(perm):
                friend_data = friends[name]
                loc = friend_data['location']
                available_start = friend_data['available_start']
                max_start = friend_data['max_start']
                # Calculate arrival time
                if i == 0:
                    # First friend: travel from Castro
                    travel_time = travel_times[('Castro', loc)]
                    arrival_time = 540 + travel_time
                else:
                    prev_name = perm[i-1]
                    prev_loc = friends[prev_name]['location']
                    travel_time = travel_times[(prev_loc, loc)]
                    # arrival_time is previous friend's end time + travel time
                    # previous friend's end time is start_prev + 90
                    arrival_time = variables[prev_name] + 90 + travel_time
                # Add constraints for current friend's start time
                constraints.append(variables[name] >= arrival_time)
                constraints.append(variables[name] >= available_start)
                constraints.append(variables[name] <= max_start)
            # Create solver and add constraints
            s = Solver()
            s.add(constraints)
            if s.check() == sat:
                model = s.model()
                itinerary = []
                for name in perm:
                    start = model[variables[name]].as_long()
                    end = start + 90
                    # Convert to HH:MM format
                    start_h = start // 60
                    start_m = start % 60
                    end_h = end // 60
                    end_m = end % 60
                    start_str = f"{start_h:02d}:{start_m:02d}"
                    end_str = f"{end_h:02d}:{end_m:02d}"
                    itinerary.append({
                        "action": "meet", 
                        "person": name, 
                        "start_time": start_str, 
                        "end_time": end_str
                    })
                print(json.dumps({"itinerary": itinerary}))
                exit()

print(json.dumps({"itinerary": []}))  # If no solution found