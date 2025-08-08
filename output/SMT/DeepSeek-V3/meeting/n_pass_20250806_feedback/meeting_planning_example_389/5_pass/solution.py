from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

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

    # Convert all times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    start_of_day = time_to_minutes("09:00")

    # Friends' availability and constraints
    friends = {
        'Sarah': {
            'location': 'Fisherman\'s Wharf',
            'available_start': time_to_minutes("14:45"),  # 2:45 PM
            'available_end': time_to_minutes("17:30"),    # 5:30 PM
            'min_duration': 105,
        },
        'Mary': {
            'location': 'Richmond District',
            'available_start': time_to_minutes("13:00"),   # 1:00 PM
            'available_end': time_to_minutes("19:15"),     # 7:15 PM
            'min_duration': 75,
        },
        'Helen': {
            'location': 'Mission District',
            'available_start': time_to_minutes("21:45"),   # 9:45 PM
            'available_end': time_to_minutes("22:30"),     # 10:30 PM
            'min_duration': 30,
        },
        'Thomas': {
            'location': 'Bayview',
            'available_start': time_to_minutes("15:15"),  # 3:15 PM
            'available_end': time_to_minutes("18:45"),    # 6:45 PM
            'min_duration': 120,
        }
    }

    # Variables for each meeting's start and end times (in minutes since 9:00 AM)
    meet_vars = {}
    for name in friends:
        meet_vars[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}')
        }

    # Variables to track arrival and departure times at each location
    arrival_times = {}
    departure_times = {}
    for name in friends:
        arrival_times[name] = Int(f'arrival_{name}')
        departure_times[name] = Int(f'departure_{name}')

    # Initial location is Haight-Ashbury at 9:00 AM (540 minutes)
    current_time = start_of_day
    current_location = 'Haight-Ashbury'

    # Create all possible meeting orders (permutations)
    from itertools import permutations
    meeting_orders = list(permutations(friends.keys()))

    # We'll try different meeting orders until we find a feasible schedule
    for order in meeting_orders:
        s.push()  # Create a new scope for this order

        # Reset current time and location
        current_time = start_of_day
        current_location = 'Haight-Ashbury'

        # Schedule meetings in this order
        for name in order:
            friend = friends[name]
            location = friend['location']
            
            # Travel to the friend's location
            travel_key = (current_location, location)
            travel_duration = travel_times[travel_key]
            
            # Arrival time at friend's location
            arrival = current_time + travel_duration
            s.add(arrival_times[name] == arrival)
            
            # Meeting must start after arrival and within friend's availability
            s.add(meet_vars[name]['start'] >= arrival)
            s.add(meet_vars[name]['start'] >= friend['available_start'])
            s.add(meet_vars[name]['end'] == meet_vars[name]['start'] + friend['min_duration'])
            s.add(meet_vars[name]['end'] <= friend['available_end'])
            
            # Departure time from friend's location
            departure = meet_vars[name]['end']
            s.add(departure_times[name] == departure)
            
            # Update current time and location for next meeting
            current_time = departure
            current_location = location

        # Helen must be last (since she's only available late)
        if order[-1] != 'Helen':
            s.pop()
            continue

        # Check if this order is feasible
        if s.check() == sat:
            model = s.model()
            itinerary = []
            
            # Collect all meetings in chronological order
            meetings = []
            for name in friends:
                start = model.evaluate(meet_vars[name]['start']).as_long()
                end = model.evaluate(meet_vars[name]['end']).as_long()
                meetings.append({
                    'name': name,
                    'start': start,
                    'end': end,
                    'location': friends[name]['location']
                })
            
            # Sort meetings by start time
            meetings.sort(key=lambda x: x['start'])
            
            # Build itinerary with travel times
            prev_location = 'Haight-Ashbury'
            prev_time = start_of_day
            for meeting in meetings:
                # Add travel to meeting location
                travel_key = (prev_location, meeting['location'])
                travel_duration = travel_times[travel_key]
                travel_start = prev_time
                travel_end = travel_start + travel_duration
                
                itinerary.append({
                    'action': 'travel',
                    'from': prev_location,
                    'to': meeting['location'],
                    'start_time': minutes_to_time(travel_start),
                    'end_time': minutes_to_time(travel_end)
                })
                
                # Add meeting
                itinerary.append({
                    'action': 'meet',
                    'person': meeting['name'],
                    'start_time': minutes_to_time(meeting['start']),
                    'end_time': minutes_to_time(meeting['end'])
                })
                
                prev_location = meeting['location']
                prev_time = meeting['end']
            
            s.pop()
            return {'itinerary': [x for x in itinerary if x['action'] == 'meet']}
        
        s.pop()  # Remove this order's constraints

    return {'error': 'No feasible schedule found'}

result = solve_scheduling_problem()
print(json.dumps(result, indent=2))