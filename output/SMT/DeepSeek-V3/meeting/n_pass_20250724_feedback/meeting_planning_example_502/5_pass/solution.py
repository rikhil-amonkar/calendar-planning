from z3 import *
import json
from itertools import permutations

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define locations and travel times
    locations = {
        'Financial District': 0,
        'Golden Gate Park': 1,
        'Chinatown': 2,
        'Union Square': 3,
        'Fisherman\'s Wharf': 4,
        'Pacific Heights': 5,
        'North Beach': 6
    }

    # Travel times matrix (from, to) -> minutes
    travel_times = [
        [0, 23, 5, 9, 10, 13, 7],
        [26, 0, 23, 22, 24, 16, 24],
        [5, 23, 0, 7, 8, 10, 3],
        [9, 22, 7, 0, 15, 15, 10],
        [11, 25, 12, 13, 0, 12, 6],
        [13, 15, 11, 12, 13, 0, 9],
        [8, 22, 6, 7, 5, 8, 0]
    ]

    # Friends' availability
    friends = {
        'Joseph': {'location': 'Pacific Heights', 'start': 8*60+15, 'end': 9*60+30, 'min_duration': 60},
        'Rebecca': {'location': 'Fisherman\'s Wharf', 'start': 8*60, 'end': 11*60+15, 'min_duration': 30},
        'Stephanie': {'location': 'Golden Gate Park', 'start': 11*60, 'end': 15*60, 'min_duration': 105},
        'Karen': {'location': 'Chinatown', 'start': 13*60+45, 'end': 16*60+30, 'min_duration': 15},
        'Steven': {'location': 'North Beach', 'start': 14*60+30, 'end': 20*60+45, 'min_duration': 120},
        'Brian': {'location': 'Union Square', 'start': 15*60, 'end': 17*60+15, 'min_duration': 30}
    }

    # Create meeting variables
    meetings = {}
    for name in friends:
        meetings[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}'),
            'location': locations[friends[name]['location']]
        }

    # Add individual meeting constraints
    for name in friends:
        s.add(meetings[name]['start'] >= friends[name]['start'])
        s.add(meetings[name]['end'] <= friends[name]['end'])
        s.add(meetings[name]['end'] - meetings[name]['start'] >= friends[name]['min_duration'])

    # Try all possible meeting orders (permutations)
    for order in permutations(friends.keys()):
        temp_solver = Solver()
        temp_solver.add(s.assertions())

        # Track time and location
        current_time = 9 * 60  # Start at Financial District at 9:00
        current_loc = locations['Financial District']

        for name in order:
            meeting = meetings[name]
            travel_time = travel_times[current_loc][meeting['location']]
            
            # Add constraints for this order
            temp_solver.add(meeting['start'] >= current_time + travel_time)
            current_time = meeting['end']
            current_loc = meeting['location']

        if temp_solver.check() == sat:
            m = temp_solver.model()
            itinerary = []
            for name in order:
                start = m[meetings[name]['start']].as_long()
                end = m[meetings[name]['end']].as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{start//60:02d}:{start%60:02d}",
                    "end_time": f"{end//60:02d}:{end%60:02d}"
                })
            return {"itinerary": itinerary}

    return {"error": "No valid schedule found"}

# Solve and print result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))