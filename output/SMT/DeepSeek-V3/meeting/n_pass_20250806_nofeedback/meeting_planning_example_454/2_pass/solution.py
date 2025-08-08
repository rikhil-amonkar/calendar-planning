from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define travel times between locations (in minutes)
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
        ('North Beach', 'Mission District'): 17,
        ('Mission District', 'Presidio'): 25,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'Bayview'): 15,
        ('Mission District', 'Chinatown'): 16,
        ('Mission District', 'North Beach'): 17,
    }

    # Friends' availability and meeting constraints
    friends = {
        'Jessica': {
            'location': 'Golden Gate Park',
            'available_start': (13, 45),  # 1:45 PM
            'available_end': (15, 0),      # 3:00 PM
            'min_duration': 30,            # minutes
        },
        'Ashley': {
            'location': 'Bayview',
            'available_start': (17, 15),    # 5:15 PM
            'available_end': (20, 0),      # 8:00 PM
            'min_duration': 105,           # minutes
        },
        'Ronald': {
            'location': 'Chinatown',
            'available_start': (7, 15),    # 7:15 AM
            'available_end': (14, 45),      # 2:45 PM
            'min_duration': 90,             # minutes
        },
        'William': {
            'location': 'North Beach',
            'available_start': (13, 15),    # 1:15 PM
            'available_end': (20, 15),      # 8:15 PM
            'min_duration': 15,             # minutes
        },
        'Daniel': {
            'location': 'Mission District',
            'available_start': (7, 0),      # 7:00 AM
            'available_end': (11, 15),      # 11:15 AM
            'min_duration': 105,           # minutes
        }
    }

    # Helper function to convert (HH, MM) to minutes
    def time_to_minutes(time):
        return time[0] * 60 + time[1]

    # Current time starts at Presidio at 9:00 AM (540 minutes)
    current_time = time_to_minutes((9, 0))
    current_location = 'Presidio'

    # Create Z3 variables for each meeting's start and end times
    meetings = {}
    for name in friends:
        meetings[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}'),
            'location': friends[name]['location'],
            'min_start': time_to_minutes(friends[name]['available_start']),
            'max_end': time_to_minutes(friends[name]['available_end']),
            'duration': friends[name]['min_duration']
        }

    # Basic meeting constraints
    for name in meetings:
        m = meetings[name]
        s.add(m['start'] >= m['min_start'])
        s.add(m['end'] <= m['max_end'])
        s.add(m['end'] == m['start'] + m['duration'])

    # We need to define the order of meetings and travel times between them
    # Let's create a list of all possible meeting orders and find one that works
    from itertools import permutations

    # We'll try all possible orders of meetings (5! = 120 possibilities)
    # To make it faster, we'll prioritize orders that make sense based on time constraints
    possible_orders = [
        ['Daniel', 'Ronald', 'Jessica', 'William', 'Ashley'],
        ['Daniel', 'Ronald', 'William', 'Jessica', 'Ashley'],
        ['Ronald', 'Daniel', 'Jessica', 'William', 'Ashley'],
        ['Ronald', 'Daniel', 'William', 'Jessica', 'Ashley'],
        ['Daniel', 'Jessica', 'Ronald', 'William', 'Ashley'],
    ]

    # Function to check if an order is feasible
    def check_order(order):
        temp_solver = Solver()
        
        # Copy all the basic constraints
        for name in meetings:
            m = meetings[name]
            temp_solver.add(m['start'] >= m['min_start'])
            temp_solver.add(m['end'] <= m['max_end'])
            temp_solver.add(m['end'] == m['start'] + m['duration'])
        
        # Add ordering constraints
        prev_end = current_time
        prev_loc = current_location
        
        for name in order:
            m = meetings[name]
            # Must start after previous meeting ends plus travel time
            travel = travel_times.get((prev_loc, m['location']), 0)
            temp_solver.add(m['start'] >= prev_end + travel)
            prev_end = m['end']
            prev_loc = m['location']
        
        if temp_solver.check() == sat:
            model = temp_solver.model()
            itinerary = []
            for name in order:
                start = model[meetings[name]['start']].as_long()
                end = model[meetings[name]['end']].as_long()
                start_hh = start // 60
                start_mm = start % 60
                end_hh = end // 60
                end_mm = end % 60
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{start_hh:02d}:{start_mm:02d}",
                    "end_time": f"{end_hh:02d}:{end_mm:02d}"
                })
            return {"itinerary": itinerary}
        return None

    # Try each possible order until we find a feasible one
    for order in possible_orders:
        result = check_order(order)
        if result:
            return result

    # If no order worked, return error
    return {"error": "No feasible schedule found"}

# Solve the scheduling problem
result = solve_scheduling()
print(json.dumps(result, indent=2))