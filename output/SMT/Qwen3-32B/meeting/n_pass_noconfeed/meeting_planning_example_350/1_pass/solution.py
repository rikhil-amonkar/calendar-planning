import z3
from itertools import permutations
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

friends = [
    {'name': 'Mary', 'location': 'Pacific Heights', 'available_start': 600, 'available_end': 1140, 'min_duration': 45},
    {'name': 'Lisa', 'location': 'Mission District', 'available_start': 1230, 'available_end': 1320, 'min_duration': 75},
    {'name': 'Betty', 'location': 'Haight-Ashbury', 'available_start': 435, 'available_end': 1035, 'min_duration': 90},
    {'name': 'Charles', 'location': 'Financial District', 'available_start': 675, 'available_end': 900, 'min_duration': 120},
]

travel_time_dict = {
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Financial District'): 19,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Financial District'): 13,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Financial District'): 17,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Mission District'): 17,
    ('Financial District', 'Haight-Ashbury'): 19,
}

itinerary = None

# Try permutations from longest to shortest
for r in range(len(friends), 0, -1):
    for perm in permutations(friends, r):
        solver = z3.Solver()
        start_vars = [z3.Int(f'start_{i}') for i in range(r)]
        
        prev_end = 540  # start time at Bayview is 9:00 AM (540 minutes)
        prev_location = 'Bayview'
        
        for i in range(r):
            current = perm[i]
            current_loc = current['location']
            travel_time = travel_time_dict[(prev_location, current_loc)]
            arrival_time = prev_end + travel_time
            available_start = current['available_start']
            lower_bound = z3.If(arrival_time >= available_start, arrival_time, available_start)
            solver.add(start_vars[i] >= lower_bound)
            
            duration = current['min_duration']
            end_time = start_vars[i] + duration
            solver.add(end_time <= current['available_end'])
            
            prev_end = end_time
            prev_location = current_loc
        
        if solver.check() == z3.sat:
            model = solver.model()
            result = []
            for i in range(r):
                start_val = model[start_vars[i]].as_long()
                end_val = start_val + perm[i]['min_duration']
                result.append({
                    "action": "meet",
                    "location": perm[i]['location'],
                    "person": perm[i]['name'],
                    "start_time": minutes_to_time(start_val),
                    "end_time": minutes_to_time(end_val)
                })
            itinerary = result
            print(json.dumps({"itinerary": itinerary}, indent=2))
            exit()

print(json.dumps({"itinerary": []}))