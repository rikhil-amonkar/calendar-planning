from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        'Haight-Ashbury': {
            'Fisherman\'s Wharf': 23,
            'Richmond District': 10,
            'Mission District': 11,
            'Bayview': 18
        },
        'Fisherman\'s Wharf': {
            'Haight-Ashbury': 22,
            'Richmond District': 18,
            'Mission District': 22,
            'Bayview': 26
        },
        'Richmond District': {
            'Haight-Ashbury': 10,
            'Fisherman\'s Wharf': 18,
            'Mission District': 20,
            'Bayview': 26
        },
        'Mission District': {
            'Haight-Ashbury': 12,
            'Fisherman\'s Wharf': 22,
            'Richmond District': 20,
            'Bayview': 15
        },
        'Bayview': {
            'Haight-Ashbury': 19,
            'Fisherman\'s Wharf': 25,
            'Richmond District': 25,
            'Mission District': 13
        }
    }

    # Friends' availability and constraints
    friends = {
        'Sarah': {
            'location': 'Fisherman\'s Wharf',
            'start': (14, 45),  # 2:45 PM
            'end': (17, 30),    # 5:30 PM
            'duration': 105    # minutes
        },
        'Mary': {
            'location': 'Richmond District',
            'start': (13, 0),   # 1:00 PM
            'end': (19, 15),    # 7:15 PM
            'duration': 75
        },
        'Helen': {
            'location': 'Mission District',
            'start': (21, 45),  # 9:45 PM
            'end': (22, 30),    # 10:30 PM
            'duration': 30
        },
        'Thomas': {
            'location': 'Bayview',
            'start': (15, 15),  # 3:15 PM
            'end': (18, 45),    # 6:45 PM
            'duration': 120
        }
    }

    # Current location and start time
    current_location = 'Haight-Ashbury'
    current_time = (9, 0)  # 9:00 AM

    # Convert all times to minutes since midnight for easier arithmetic
    def time_to_minutes(h, m):
        return h * 60 + m

    # Convert minutes back to (h, m)
    def minutes_to_time(t):
        return (t // 60, t % 60)

    # Initialize variables for each meeting's start and end times
    meeting_vars = {}
    for name in friends:
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        meeting_vars[name] = {
            'start': start_var,
            'end': end_var,
            'location': friends[name]['location'],
            'duration': friends[name]['duration'],
            'window_start': time_to_minutes(*friends[name]['start']),
            'window_end': time_to_minutes(*friends[name]['end'])
        }
        # Constrain meeting within friend's window
        s.add(start_var >= meeting_vars[name]['window_start'])
        s.add(end_var <= meeting_vars[name]['window_end'])
        s.add(end_var == start_var + meeting_vars[name]['duration'])

    # Generate all possible permutations of meeting orders
    from itertools import permutations
    friend_names = list(friends.keys())
    possible_orders = list(permutations(friend_names))

    # Try each possible order until we find a feasible schedule
    for order in possible_orders:
        temp_solver = Solver()
        
        # Copy all meeting constraints
        for name in meeting_vars:
            temp_solver.add(meeting_vars[name]['start'] >= meeting_vars[name]['window_start'])
            temp_solver.add(meeting_vars[name]['end'] <= meeting_vars[name]['window_end'])
            temp_solver.add(meeting_vars[name]['end'] == meeting_vars[name]['start'] + meeting_vars[name]['duration'])

        # Add travel time constraints for this specific order
        prev_location = current_location
        prev_end = time_to_minutes(*current_time)
        
        for i, name in enumerate(order):
            # Travel time from previous location to current meeting
            travel_time = travel_times[prev_location][friends[name]['location']]
            temp_solver.add(meeting_vars[name]['start'] >= prev_end + travel_time)
            
            # Update for next iteration
            prev_location = friends[name]['location']
            prev_end = meeting_vars[name]['end']

        # Check if this order works
        if temp_solver.check() == sat:
            m = temp_solver.model()
            # Build itinerary
            itinerary = []
            for name in order:
                start = m.evaluate(meeting_vars[name]['start']).as_long()
                end = m.evaluate(meeting_vars[name]['end']).as_long()
                start_h, start_m = minutes_to_time(start)
                end_h, end_m = minutes_to_time(end)
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{start_h:02d}:{start_m:02d}",
                    "end_time": f"{end_h:02d}:{end_m:02d}"
                })
            return {"itinerary": itinerary}

    return {"error": "No feasible schedule found"}

result = solve_scheduling()
print(json.dumps(result, indent=2))