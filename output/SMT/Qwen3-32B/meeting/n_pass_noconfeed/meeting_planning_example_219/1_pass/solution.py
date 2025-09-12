import itertools
from z3 import *
import json

# Define travel times between locations
travel_time = {
    ('Castro', 'Alamo Square'): 8,
    ('Castro', 'Union Square'): 19,
    ('Castro', 'Chinatown'): 20,
    ('Alamo Square', 'Castro'): 8,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Chinatown'): 16,
    ('Union Square', 'Castro'): 19,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Chinatown', 'Castro'): 22,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Union Square'): 7,
}

# Define friend constraints
friends_data = {
    'Emily': {
        'location': 'Alamo Square',
        'available_start': 705,  # 11:45 AM
        'available_end': 915,    # 3:15 PM
        'min_duration': 105
    },
    'Barbara': {
        'location': 'Union Square',
        'available_start': 1005, # 4:45 PM
        'available_end': 1095,   # 6:15 PM
        'min_duration': 60
    },
    'William': {
        'location': 'Chinatown',
        'available_start': 1035, # 5:15 PM
        'available_end': 1140,   # 7:00 PM
        'min_duration': 105
    }
}

friends = ['Emily', 'Barbara', 'William']
best_solution = None
best_length = 0

for length in [3, 2, 1]:
    for perm in itertools.permutations(friends, length):
        solver = Solver()
        prev_location = 'Castro'
        prev_end = 540  # Start at 9:00 AM (540 minutes)
        for i, friend in enumerate(perm):
            friend_info = friends_data[friend]
            current_location = friend_info['location']
            available_start = friend_info['available_start']
            available_end = friend_info['available_end']
            min_duration = friend_info['min_duration']
            travel = travel_time[(prev_location, current_location)]
            arrival_time = prev_end + travel
            s = Int(f's_{friend}_{i}')
            solver.add(s >= arrival_time)
            solver.add(s >= available_start)
            solver.add(s + min_duration <= available_end)
            prev_end = s + min_duration
            prev_location = current_location
        if solver.check() == sat:
            model = solver.model()
            itinerary = []
            prev_loc = 'Castro'
            prev_time = 540
            for i, friend in enumerate(perm):
                friend_info = friends_data[friend]
                current_loc = friend_info['location']
                s = model.evaluate(Int(f's_{friend}_{i}'))
                end_time = s + friend_info['min_duration']
                start_hm = f"{(s // 60)}:{(s % 60):02d}"
                end_hm = f"{(end_time // 60)}:{(end_time % 60):02d}"
                itinerary.append({
                    "action": "meet",
                    "location": current_loc,
                    "person": friend,
                    "start_time": start_hm,
                    "end_time": end_hm
                })
                prev_time = end_time
                prev_loc = current_loc
            if len(perm) > best_length:
                best_solution = itinerary
                best_length = len(perm)

result = {"itinerary": best_solution if best_solution else []}
print(json.dumps(result, indent=2))