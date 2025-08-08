from z3 import *
import json
from itertools import permutations

def solve_scheduling_problem():
    # Travel times between locations (in minutes)
    travel_times = {
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'Financial District'): 23,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'Financial District'): 22,
        ('Financial District', 'Presidio'): 22,
        ('Financial District', 'Richmond District'): 21,
    }

    # Friends' availability and minimum meeting durations
    friends = {
        'Emily': {
            'location': 'Presidio',
            'available_start': 15 * 60 + 15,  # 4:15 PM in minutes since 9:00 AM (375)
            'available_end': 21 * 60,         # 9:00 PM (720)
            'min_duration': 105,
        },
        'Joseph': {
            'location': 'Richmond District',
            'available_start': 17 * 60 + 15,  # 5:15 PM (495)
            'available_end': 22 * 60,         # 10:00 PM (780)
            'min_duration': 120,
        },
        'Melissa': {
            'location': 'Financial District',
            'available_start': 15 * 60 + 45,  # 3:45 PM (405)
            'available_end': 21 * 60 + 45,    # 9:45 PM (765)
            'min_duration': 75,
        }
    }

    # All possible meeting orders
    meeting_orders = permutations(friends.keys())

    for order in meeting_orders:
        s = Solver()

        # Variables for start and end times of each meeting (in minutes since 9:00 AM)
        times = {name: {'start': Int(f'{name}_start'), 'end': Int(f'{name}_end')} for name in friends}

        # Add constraints for each friend's availability and minimum duration
        for name in friends:
            info = friends[name]
            s.add(times[name]['end'] - times[name]['start'] >= info['min_duration'])
            s.add(times[name]['start'] >= info['available_start'])
            s.add(times[name]['end'] <= info['available_end'])

        # Initial location is Fisherman's Wharf
        current_location = 'Fisherman\'s Wharf'

        # Add constraints for travel times between meetings
        prev_end = 0  # Starting time is 9:00 AM (0 minutes since 9:00 AM)
        for i, name in enumerate(order):
            # Travel from current_location to friend's location
            travel_time = travel_times.get((current_location, friends[name]['location']), 0)
            s.add(times[name]['start'] >= prev_end + travel_time)
            prev_end = times[name]['end']
            current_location = friends[name]['location']

        # Check if the current order is feasible
        if s.check() == sat:
            model = s.model()
            itinerary = []

            # Convert minutes since 9:00 AM to HH:MM format
            def minutes_to_time(minutes):
                total_minutes = minutes
                hours = total_minutes // 60
                mins = total_minutes % 60
                # Ensure hours are within 0-23
                hours = hours % 24
                return f"{hours:02d}:{mins:02d}"

            valid = True
            for name in order:
                start = model.evaluate(times[name]['start']).as_long()
                end = model.evaluate(times[name]['end']).as_long()
                start_time = minutes_to_time(start)
                end_time = minutes_to_time(end)
                # Ensure the times are within the friend's availability window
                if start < friends[name]['available_start'] or end > friends[name]['available_end']:
                    valid = False
                    break
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_time,
                    "end_time": end_time
                })

            if valid:
                return {"itinerary": itinerary}

    return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))