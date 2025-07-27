from z3 import *
import json
from itertools import permutations

def solve_scheduling_problem():
    # Define travel times between locations (in minutes)
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

    # Define friends and their constraints
    friends = [
        {
            'name': 'Sarah',
            'location': 'Fisherman\'s Wharf',
            'available_start': (14, 45),  # 2:45 PM
            'available_end': (17, 30),    # 5:30 PM
            'min_duration': 105,
        },
        {
            'name': 'Mary',
            'location': 'Richmond District',
            'available_start': (13, 0),   # 1:00 PM
            'available_end': (19, 15),    # 7:15 PM
            'min_duration': 75,
        },
        {
            'name': 'Helen',
            'location': 'Mission District',
            'available_start': (21, 45),  # 9:45 PM
            'available_end': (22, 30),    # 10:30 PM
            'min_duration': 30,
        },
        {
            'name': 'Thomas',
            'location': 'Bayview',
            'available_start': (15, 15),  # 3:15 PM
            'available_end': (18, 45),    # 6:45 PM
            'min_duration': 120,
        }
    ]

    # Convert times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(hour, minute):
        return hour * 60 + minute - 540

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        total_minutes = 540 + minutes
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"

    # Try all possible meeting orders (permutations)
    for order in permutations(friends):
        s = Solver()

        # Create variables for each meeting's start and end times
        meeting_vars = {}
        for friend in order:
            name = friend['name']
            start = Int(f'start_{name}')
            end = Int(f'end_{name}')
            meeting_vars[name] = (start, end, friend['location'])

            # Meeting must be within friend's availability
            s.add(start >= time_to_minutes(*friend['available_start']))
            s.add(end <= time_to_minutes(*friend['available_end']))
            s.add(end - start >= friend['min_duration'])

        # Starting point
        current_location = 'Haight-Ashbury'
        current_time = 0

        # Schedule meetings in the current order
        prev_end = 0
        for i, friend in enumerate(order):
            name = friend['name']
            start, end, location = meeting_vars[name]
            
            # Travel time from previous location to current meeting
            if i == 0:
                travel_time = travel_times.get((current_location, location), 0)
            else:
                prev_location = order[i-1]['location']
                travel_time = travel_times.get((prev_location, location), 0)
            
            # Meeting must start after previous meeting ends plus travel time
            if i == 0:
                s.add(start >= current_time + travel_time)
            else:
                prev_name = order[i-1]['name']
                s.add(start >= meeting_vars[prev_name][1] + travel_time)

        # Check if this order works
        if s.check() == sat:
            model = s.model()
            itinerary = []
            for friend in order:
                name = friend['name']
                start = model.eval(meeting_vars[name][0]).as_long()
                end = model.eval(meeting_vars[name][1]).as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
            # Sort by start time
            itinerary.sort(key=lambda x: x['start_time'])
            return {"itinerary": itinerary}

    # If no solution found
    return {"itinerary": []}

# Solve and print solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))