from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Define travel times (in minutes) between locations
    travel_times = {
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Bayview'): 31,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Mission District'): 26,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Bayview', 'Presidio'): 31,
        ('Bayview', 'Golden Gate Park'): 22,
        ('Bayview', 'Chinatown'): 18,
        ('Bayview', 'North Beach'): 21,
        ('Bayview', 'Mission District'): 13,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Bayview'): 22,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Mission District'): 18,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Bayview'): 22,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Mission District'): 18,
        ('Mission District', 'Presidio'): 25,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'Bayview'): 15,
        ('Mission District', 'Chinatown'): 16,
        ('Mission District', 'North Beach'): 17,
    }

    # Friend availability and constraints
    friends = {
        'Jessica': {'location': 'Golden Gate Park', 'start': (13, 45), 'end': (15, 0), 'min_duration': 30},
        'Ashley': {'location': 'Bayview', 'start': (17, 15), 'end': (20, 0), 'min_duration': 105},
        'Ronald': {'location': 'Chinatown', 'start': (7, 15), 'end': (14, 45), 'min_duration': 90},
        'William': {'location': 'North Beach', 'start': (13, 15), 'end': (20, 15), 'min_duration': 15},
        'Daniel': {'location': 'Mission District', 'start': (7, 0), 'end': (11, 15), 'min_duration': 105},
    }

    # Convert friend availability to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(h, m):
        return h * 60 + m

    friend_minutes = {}
    for name, data in friends.items():
        start_min = time_to_minutes(data['start'][0], data['start'][1]) - 540  # Relative to 9:00 AM
        end_min = time_to_minutes(data['end'][0], data['end'][1]) - 540
        friend_minutes[name] = {
            'start': start_min,
            'end': end_min,
            'min_duration': data['min_duration'],
            'location': data['location']
        }

    # Variables for each meeting: start and end times in minutes since 9:00 AM
    meeting_vars = {}
    for name in friends:
        meeting_vars[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}'),
            'met': Bool(f'met_{name}')
        }

    # Constraints for each meeting
    for name in friends:
        data = friend_minutes[name]
        opt.add(Implies(meeting_vars[name]['met'], 
                      And(meeting_vars[name]['start'] >= data['start'],
                          meeting_vars[name]['end'] <= data['end'],
                          meeting_vars[name]['end'] - meeting_vars[name]['start'] >= data['min_duration'])))

    # Create a list of all possible meeting orders
    from itertools import permutations
    meeting_names = list(friends.keys())
    possible_orders = permutations(meeting_names)

    # Try different meeting orders to find a valid schedule
    for order in possible_orders:
        # Reset the optimizer for each order
        opt.push()
        
        # Add travel time constraints for this order
        for i in range(len(order)-1):
            current = order[i]
            next_ = order[i+1]
            if is_true(opt.check()):
                # Only add constraints if both meetings are being scheduled
                opt.add(Implies(And(meeting_vars[current]['met'], meeting_vars[next_]['met']),
                              meeting_vars[next_]['start'] >= meeting_vars[current]['end'] + 
                              travel_times.get((friend_minutes[current]['location'], friend_minutes[next_]['location']), 0)))
        
        # Maximize the number of friends met
        opt.maximize(Sum([If(meeting_vars[name]['met'], 1, 0) for name in friends]))
        
        # Check if a solution exists
        if opt.check() == sat:
            model = opt.model()
            itinerary = []
            valid = True
            # Verify all travel times are satisfied
            for i in range(len(order)-1):
                current = order[i]
                next_ = order[i+1]
                if is_true(model[meeting_vars[current]['met']]) and is_true(model[meeting_vars[next_]['met']]):
                    travel_time = travel_times.get((friend_minutes[current]['location'], friend_minutes[next_]['location']), 0)
                    if model[meeting_vars[next_]['start']].as_long() < model[meeting_vars[current]['end']].as_long() + travel_time:
                        valid = False
                        break
            if valid:
                for name in friends:
                    if is_true(model[meeting_vars[name]['met']]):
                        start = model[meeting_vars[name]['start']].as_long()
                        end = model[meeting_vars[name]['end']].as_long()
                        # Convert minutes back to HH:MM format
                        start_h = (start + 540) // 60
                        start_m = (start + 540) % 60
                        end_h = (end + 540) // 60
                        end_m = (end + 540) % 60
                        itinerary.append({
                            "action": "meet",
                            "person": name,
                            "start_time": f"{start_h:02d}:{start_m:02d}",
                            "end_time": f"{end_h:02d}:{end_m:02d}"
                        })
                opt.pop()
                return {"itinerary": itinerary}
        opt.pop()

    return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))