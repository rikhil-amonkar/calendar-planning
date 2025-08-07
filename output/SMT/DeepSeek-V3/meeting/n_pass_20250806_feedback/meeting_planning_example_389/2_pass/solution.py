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

    # Initial location is Haight-Ashbury at 9:00 AM (540 minutes)
    current_location = 'Haight-Ashbury'
    current_time = start_of_day

    # To model the sequence of meetings, we need to decide the order in which to meet the friends.
    # Since Helen is only available very late, we can schedule her last.
    # The others can be scheduled in any order, considering travel times.

    # Define the meeting order (this is a heuristic; the solver will adjust times to fit)
    meeting_order = ['Mary', 'Sarah', 'Thomas', 'Helen']

    # Create variables for the start and end times of each action (meet or travel)
    actions = []
    prev_location = current_location
    prev_end_time = current_time

    for name in meeting_order:
        friend = friends[name]
        location = friend['location']
        
        # Travel to the friend's location
        travel_key = (prev_location, location)
        travel_duration = travel_times[travel_key]
        
        # Travel starts at prev_end_time
        travel_start = prev_end_time
        travel_end = travel_start + travel_duration
        
        # Meeting starts after travel ends
        meet_start = meet_vars[name]['start']
        meet_end = meet_vars[name]['end']
        
        s.add(meet_start >= travel_end)
        s.add(meet_end == meet_start + friend['min_duration'])
        s.add(meet_start >= friend['available_start'])
        s.add(meet_end <= friend['available_end'])
        
        # Update previous location and time
        prev_location = location
        prev_end_time = meet_end
        
        # Add to actions
        actions.append({
            'action': 'travel',
            'from': prev_location if name != meeting_order[0] else 'Haight-Ashbury',
            'to': location,
            'start_time': travel_start,
            'end_time': travel_end
        })
        actions.append({
            'action': 'meet',
            'person': name,
            'start_time': meet_start,
            'end_time': meet_end
        })

    # Also, ensure no overlapping meetings (but since we're doing them in sequence, it's handled)
    
    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        for action in actions:
            if action['action'] == 'meet':
                start = model.evaluate(meet_vars[action['person']]['start']).as_long()
                end = model.evaluate(meet_vars[action['person']]['end']).as_long()
                itinerary.append({
                    'action': 'meet',
                    'person': action['person'],
                    'start_time': minutes_to_time(start),
                    'end_time': minutes_to_time(end)
                })
        
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x['start_time']))
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No feasible schedule found'}

result = solve_scheduling_problem()
print(json.dumps(result, indent=2))