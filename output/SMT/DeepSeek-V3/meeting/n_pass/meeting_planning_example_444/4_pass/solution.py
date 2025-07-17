from z3 import *
import json

def solve_scheduling():
    # Initialize solver with better configuration
    s = Solver()
    s.set("timeout", 30000)  # Give more time to find solution

    # Define locations and travel times (in minutes)
    locations = {
        'Financial District': 0,
        'Russian Hill': 1,
        'Sunset District': 2,
        'North Beach': 3,
        'The Castro': 4,
        'Golden Gate Park': 5
    }

    # Travel times matrix
    travel_times = [
        [0, 10, 31, 7, 23, 23],
        [11, 0, 23, 5, 21, 21],
        [30, 24, 0, 29, 17, 11],
        [8, 4, 27, 0, 22, 22],
        [20, 18, 17, 20, 0, 11],
        [26, 19, 10, 24, 13, 0]
    ]

    # Friends' data with adjusted constraints
    friends = [
        {'name': 'Ronald', 'location': 'Russian Hill', 'start': (13, 45), 'end': (17, 15), 'min_duration': 105},
        {'name': 'Patricia', 'location': 'Sunset District', 'start': (9, 15), 'end': (22, 0), 'min_duration': 60},
        {'name': 'Laura', 'location': 'North Beach', 'start': (12, 30), 'end': (12, 45), 'min_duration': 15},
        {'name': 'Emily', 'location': 'The Castro', 'start': (16, 15), 'end': (18, 30), 'min_duration': 60},
        {'name': 'Mary', 'location': 'Golden Gate Park', 'start': (15, 0), 'end': (16, 30), 'min_duration': 60}
    ]

    # Time conversion functions
    def time_to_minutes(hour, minute):
        return hour * 60 + minute - 540  # 9:00 AM is 540 minutes

    def minutes_to_time(m):
        total_minutes = 540 + m
        h = total_minutes // 60
        mi = total_minutes % 60
        return f"{h:02d}:{mi:02d}"

    # Create variables and basic constraints
    friend_vars = []
    for friend in friends:
        start_min = time_to_minutes(friend['start'][0], friend['start'][1])
        end_min = time_to_minutes(friend['end'][0], friend['end'][1])
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        s.add(start >= start_min)
        s.add(end <= end_min)
        s.add(end - start >= friend['min_duration'])
        friend_vars.append({
            'name': friend['name'],
            'location': friend['location'],
            'start': start,
            'end': end
        })

    # Additional constraints for travel time and ordering
    # Try different meeting orders to find a feasible solution
    orders = [
        ['Laura', 'Mary', 'Ronald', 'Emily', 'Patricia'],
        ['Laura', 'Patricia', 'Mary', 'Ronald', 'Emily'],
        ['Laura', 'Mary', 'Patricia', 'Ronald', 'Emily'],
        ['Laura', 'Ronald', 'Mary', 'Emily', 'Patricia']
    ]

    # Try different meeting orders until we find a solution
    for order in orders:
        temp_solver = Solver()
        temp_solver.set("timeout", 30000)
        
        # Add all basic constraints
        for f in friend_vars:
            temp_solver.add(f['start'] >= time_to_minutes(
                next(fr['start'] for fr in friends if fr['name'] == f['name'])[0],
                next(fr['start'] for fr in friends if fr['name'] == f['name'])[1]
            ))
            temp_solver.add(f['end'] <= time_to_minutes(
                next(fr['end'] for fr in friends if fr['name'] == f['name'])[0],
                next(fr['end'] for fr in friends if fr['name'] == f['name'])[1]
            ))
            temp_solver.add(f['end'] - f['start'] >= next(
                fr['min_duration'] for fr in friends if fr['name'] == f['name']
            ))

        # Add ordering constraints
        for i in range(len(order)-1):
            f1 = next(f for f in friend_vars if f['name'] == order[i])
            f2 = next(f for f in friend_vars if f['name'] == order[i+1])
            loc1 = locations[f1['location']]
            loc2 = locations[f2['location']]
            travel = travel_times[loc1][loc2]
            temp_solver.add(f1['end'] + travel <= f2['start'])

        if temp_solver.check() == sat:
            model = temp_solver.model()
            itinerary = []
            for friend in friend_vars:
                start_val = model[friend['start']].as_long()
                end_val = model[friend['end']].as_long()
                itinerary.append({
                    "action": "meet",
                    "person": friend['name'],
                    "start_time": minutes_to_time(start_val),
                    "end_time": minutes_to_time(end_val)
                })
            itinerary.sort(key=lambda x: x['start_time'])
            return {"itinerary": itinerary}

    return {"itinerary": []}

# Solve and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))