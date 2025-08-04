from z3 import *
import json
from itertools import permutations

def solve_scheduling_problem():
    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        'Pacific Heights': {
            'North Beach': 9,
            'Financial District': 13,
            'Alamo Square': 10,
            'Mission District': 15
        },
        'North Beach': {
            'Pacific Heights': 8,
            'Financial District': 8,
            'Alamo Square': 16,
            'Mission District': 18
        },
        'Financial District': {
            'Pacific Heights': 13,
            'North Beach': 7,
            'Alamo Square': 17,
            'Mission District': 17
        },
        'Alamo Square': {
            'Pacific Heights': 10,
            'North Beach': 15,
            'Financial District': 17,
            'Mission District': 10
        },
        'Mission District': {
            'Pacific Heights': 16,
            'North Beach': 17,
            'Financial District': 17,
            'Alamo Square': 11
        }
    }

    # Friend information
    friends = {
        'Helen': {
            'location': 'North Beach',
            'window': (540, 1020),  # 9:00-17:00
            'min_duration': 15
        },
        'Kevin': {
            'location': 'Mission District',
            'window': (645, 885),   # 10:45-14:45
            'min_duration': 45
        },
        'Amanda': {
            'location': 'Alamo Square',
            'window': (1185, 1260),  # 19:45-21:00
            'min_duration': 60
        },
        'Betty': {
            'location': 'Financial District',
            'window': (1140, 1305),  # 19:00-21:45
            'min_duration': 90
        }
    }

    # Generate all possible meeting orders (permutations)
    friend_names = list(friends.keys())
    for order in permutations(friend_names):
        s = Solver()
        
        # Create variables for each meeting's start and end times
        times = {}
        for name in order:
            times[f'{name}_start'] = Int(f'{name}_start')
            times[f'{name}_end'] = Int(f'{name}_end')
        
        # Add constraints for each meeting
        for i, name in enumerate(order):
            friend = friends[name]
            # Meeting must be within friend's window
            s.add(times[f'{name}_start'] >= friend['window'][0])
            s.add(times[f'{name}_end'] <= friend['window'][1])
            # Meeting must last at least min_duration
            s.add(times[f'{name}_end'] - times[f'{name}_start'] >= friend['min_duration'])
            
            # Travel time constraints
            if i == 0:
                # First meeting: travel from Pacific Heights
                travel = travel_times['Pacific Heights'][friend['location']]
                s.add(times[f'{name}_start'] >= 540 + travel)
            else:
                # Subsequent meetings: travel from previous location
                prev_name = order[i-1]
                prev_location = friends[prev_name]['location']
                travel = travel_times[prev_location][friend['location']]
                s.add(times[f'{name}_start'] >= times[f'{prev_name}_end'] + travel)
        
        # Check if this order is feasible
        if s.check() == sat:
            m = s.model()
            
            # Convert minutes to HH:MM format
            def minutes_to_time(minutes):
                h = minutes // 60
                m = minutes % 60
                return f"{h:02d}:{m:02d}"
            
            # Build itinerary in the order of meetings
            itinerary = []
            for name in order:
                start = m.eval(times[f'{name}_start']).as_long()
                end = m.eval(times[f'{name}_end']).as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
            
            return {"itinerary": itinerary}
    
    return {"error": "No feasible schedule found"}

result = solve_scheduling_problem()
print(json.dumps(result, indent=2))