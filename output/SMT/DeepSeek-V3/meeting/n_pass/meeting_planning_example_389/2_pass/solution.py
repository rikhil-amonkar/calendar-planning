from z3 import *
import json
from itertools import permutations

def solve_scheduling_problem():
    # Define the travel times between locations (in minutes)
    travel_times = {
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
        ('Haight-Ashbury', 'Richmond District'): 10,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Fisherman\'s Wharf', 'Mission District'): 22,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Richmond District', 'Haight-Ashbury'): 10,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Mission District'): 20,
        ('Richmond District', 'Bayview'): 26,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Fisherman\'s Wharf'): 22,
        ('Mission District', 'Richmond District'): 20,
        ('Mission District', 'Bayview'): 15,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Richmond District'): 25,
        ('Bayview', 'Mission District'): 13,
    }

    # Define the friends and their constraints
    friends = [
        {
            'name': 'Sarah',
            'location': 'Fisherman\'s Wharf',
            'available_start': (14, 45),  # 2:45 PM
            'available_end': (17, 30),    # 5:30 PM
            'min_duration': 105,         # minutes
        },
        {
            'name': 'Mary',
            'location': 'Richmond District',
            'available_start': (13, 0),   # 1:00 PM
            'available_end': (19, 15),    # 7:15 PM
            'min_duration': 75,          # minutes
        },
        {
            'name': 'Helen',
            'location': 'Mission District',
            'available_start': (21, 45),  # 9:45 PM
            'available_end': (22, 30),    # 10:30 PM
            'min_duration': 30,           # minutes
        },
        {
            'name': 'Thomas',
            'location': 'Bayview',
            'available_start': (15, 15),  # 3:15 PM
            'available_end': (18, 45),    # 6:45 PM
            'min_duration': 120,          # minutes
        }
    ]

    # Convert times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(hour, minute):
        return hour * 60 + minute - 540  # 9:00 AM is 540 minutes

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        total_minutes = 540 + minutes
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"

    # Try all possible meeting orders (permutations)
    for order in permutations(['Sarah', 'Mary', 'Thomas', 'Helen']):
        s = Solver()

        # Create variables for each meeting's start and end times
        meeting_vars = {}
        for friend in friends:
            name = friend['name']
            start = Int(f'start_{name}')
            end = Int(f'end_{name}')
            meeting_vars[name] = (start, end)
            # Constrain the meeting to be within the friend's availability
            s.add(start >= time_to_minutes(*friend['available_start']))
            s.add(end <= time_to_minutes(*friend['available_end']))
            # Constrain the meeting duration
            s.add(end - start >= friend['min_duration'])

        # Starting at Haight-Ashbury at 9:00 AM (0 minutes)
        current_location = 'Haight-Ashbury'
        current_time = 0

        # Schedule meetings in the current order
        for i, name in enumerate(order):
            friend = next(f for f in friends if f['name'] == name)
            start, end = meeting_vars[name]
            # Travel time from current_location to friend's location
            travel_time = travel_times.get((current_location, friend['location']), 0)
            # Meeting must start after current_time + travel_time
            s.add(start >= current_time + travel_time)
            # Update current_time and current_location
            current_time = end
            current_location = friend['location']

        # Check if this order works
        if s.check() == sat:
            model = s.model()
            itinerary = []
            for friend in friends:
                name = friend['name']
                start, end = meeting_vars[name]
                start_time = model.eval(start).as_long()
                end_time = model.eval(end).as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time)
                })
            # Sort the itinerary by start time
            itinerary.sort(key=lambda x: x['start_time'])
            return {"itinerary": itinerary}

    # If no solution found
    return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))