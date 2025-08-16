import itertools
from z3 import Solver, Int, sat
import json

friends = {
    'Melissa': {
        'location': 'G',
        'available_start': 8 * 60 + 30,
        'available_end': 20 * 60,
        'duration': 15
    },
    'Emily': {
        'location': 'R',
        'available_start': 16 * 60 + 45,
        'available_end': 22 * 60,
        'duration': 120
    },
    'Nancy': {
        'location': 'P',
        'available_start': 19 * 60 + 45,
        'available_end': 22 * 60,
        'duration': 105
    }
}

travel_times = {
    ('FW', 'G'): 25,
    ('FW', 'P'): 17,
    ('FW', 'R'): 18,
    ('G', 'FW'): 24,
    ('G', 'P'): 11,
    ('G', 'R'): 7,
    ('P', 'FW'): 19,
    ('P', 'G'): 12,
    ('P', 'R'): 7,
    ('R', 'FW'): 18,
    ('R', 'G'): 9,
    ('R', 'P'): 7,
}

friends_list = ['Melissa', 'Emily', 'Nancy']

for perm in itertools.permutations(friends_list):
    solver = Solver()
    s_vars = [Int(f's_{i}') for i in range(len(perm))]
    
    prev_location = 'FW'
    current_time = 540  # 9:00 AM in minutes
    
    for i, friend in enumerate(perm):
        loc = friends[friend]['location']
        travel_time = travel_times[(prev_location, loc)]
        arrival_time = current_time + travel_time
        
        s = s_vars[i]
        available_start = friends[friend]['available_start']
        duration = friends[friend]['duration']
        available_end = friends[friend]['available_end']
        
        solver.add(s >= arrival_time)
        solver.add(s >= available_start)
        solver.add(s + duration <= available_end)
        
        current_time = s + duration
        prev_location = loc
    
    if solver.check() == sat:
        model = solver.model()
        start_times = [model.evaluate(s).as_long() for s in s_vars]
        itinerary = []
        for i in range(len(perm)):
            friend = perm[i]
            start = start_times[i]
            end = start + friends[friend]['duration']
            start_time_str = f"{(start // 60):02d}:{(start % 60):02d}"
            end_time_str = f"{(end // 60):02d}:{(end % 60):02d}"
            itinerary.append({
                "action": "meet",
                "person": friend,
                "start_time": start_time_str,
                "end_time": end_time_str
            })
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result))
        break