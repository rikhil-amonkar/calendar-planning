from itertools import permutations, combinations
from z3 import Solver, Int, sat, ModelRef
import json

friends = [
    {
        'name': 'Helen',
        'location': 'North Beach',
        'available_start': 540,  # 9:00 AM
        'available_end': 1020,   # 5:00 PM
        'min_duration': 15,
    },
    {
        'name': 'Kevin',
        'location': 'Mission District',
        'available_start': 645,  # 10:45 AM
        'available_end': 885,    # 2:45 PM
        'min_duration': 45,
    },
    {
        'name': 'Amanda',
        'location': 'Alamo Square',
        'available_start': 1185, # 7:45 PM
        'available_end': 1260,   # 9:00 PM
        'min_duration': 60,
    },
    {
        'name': 'Betty',
        'location': 'Financial District',
        'available_start': 1140, # 7:00 PM
        'available_end': 1305,   # 9:45 PM
        'min_duration': 90,
    },
]

travel_times = {
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Mission District'): 15,
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Mission District'): 18,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Mission District'): 17,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Mission District'): 10,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Financial District'): 17,
    ('Mission District', 'Alamo Square'): 11,
}

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

for k in range(4, 0, -1):
    for combo in combinations(friends, k):
        for perm in permutations(combo):
            solver = Solver()
            starts = [Int(f'start_{i}') for i in range(k)]
            prev_end = 540  # arrival time at Pacific Heights
            prev_loc = 'Pacific Heights'
            for i in range(k):
                friend = perm[i]
                loc = friend['location']
                travel_time = travel_times[(prev_loc, loc)]
                solver.add(starts[i] >= prev_end + travel_time)
                solver.add(starts[i] >= friend['available_start'])
                solver.add(starts[i] + friend['min_duration'] <= friend['available_end'])
                prev_end = starts[i] + friend['min_duration']
                prev_loc = loc
            if solver.check() == sat:
                model = solver.model()
                itinerary = []
                for i in range(k):
                    friend = perm[i]
                    start_val = model.evaluate(starts[i]).as_long()
                    end_val = start_val + friend['min_duration']
                    start_time = minutes_to_time(start_val)
                    end_time = minutes_to_time(end_val)
                    itinerary.append({
                        "action": "meet",
                        "person": friend['name'],
                        "start_time": start_time,
                        "end_time": end_time
                    })
                print(json.dumps({"itinerary": itinerary}))
                exit()

print(json.dumps({"itinerary": []}))