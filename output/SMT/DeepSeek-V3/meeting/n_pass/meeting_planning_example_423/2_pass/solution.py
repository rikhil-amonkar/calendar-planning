from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define travel times (in minutes) between locations
    travel_times = {
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Financial District'): 23,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Union Square'): 22,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'North Beach'): 17,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Richmond District', 'Union Square'): 21,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Richmond District'): 18,
        ('North Beach', 'Financial District'): 8,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Union Square'): 7,
        ('Financial District', 'Presidio'): 22,
        ('Financial District', 'Richmond District'): 21,
        ('Financial District', 'North Beach'): 7,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Union Square'): 9,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'Richmond District'): 20,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Financial District'): 9,
        ('Union Square', 'Golden Gate Park'): 22,
    }

    # Friends' availability and constraints
    friends = {
        'Jason': {
            'location': 'Richmond District',
            'start': 13 * 60,  # 1:00 PM in minutes
            'end': 20 * 60 + 45,  # 8:45 PM in minutes
            'duration': 90  # minutes
        },
        'Melissa': {
            'location': 'North Beach',
            'start': 18 * 60 + 45,  # 6:45 PM in minutes
            'end': 20 * 60 + 15,  # 8:15 PM in minutes
            'duration': 45  # minutes
        },
        'Brian': {
            'location': 'Financial District',
            'start': 9 * 60 + 45,  # 9:45 AM in minutes
            'end': 21 * 60 + 45,  # 9:45 PM in minutes
            'duration': 15  # minutes
        },
        'Elizabeth': {
            'location': 'Golden Gate Park',
            'start': 8 * 60 + 45,  # 8:45 AM in minutes
            'end': 21 * 60 + 30,  # 9:30 PM in minutes
            'duration': 105  # minutes
        },
        'Laura': {
            'location': 'Union Square',
            'start': 14 * 60 + 15,  # 2:15 PM in minutes
            'end': 19 * 60 + 30,  # 7:30 PM in minutes
            'duration': 75  # minutes
        }
    }

    # Current location starts at Presidio at 9:00 AM (540 minutes)
    current_time = 9 * 60  # 9:00 AM in minutes
    current_location = 'Presidio'

    # Define variables for each meeting's start and end times
    meetings = {}
    for name in friends:
        meetings[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}')
        }

    # Add constraints for each friend's meeting
    for name in friends:
        friend = friends[name]
        start = meetings[name]['start']
        end = meetings[name]['end']
        s.add(start >= friend['start'])
        s.add(end <= friend['end'])
        s.add(end == start + friend['duration'])

    # Define the order of meetings to try
    # We'll try to meet Brian first (earliest available), then Elizabeth, Laura, Jason, Melissa
    order = ['Brian', 'Elizabeth', 'Laura', 'Jason', 'Melissa']

    # Add constraints for travel times between meetings
    prev_end = current_time
    prev_location = current_location
    for name in order:
        friend = friends[name]
        start = meetings[name]['start']
        end = meetings[name]['end']
        travel_time = travel_times.get((prev_location, friend['location']), 0)
        s.add(start >= prev_end + travel_time)
        prev_end = end
        prev_location = friend['location']

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in order:
            start_val = model[meetings[name]['start']].as_long()
            end_val = model[meetings[name]['end']].as_long()
            start_hh = start_val // 60
            start_mm = start_val % 60
            end_hh = end_val // 60
            end_mm = end_val % 60
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{start_hh:02d}:{start_mm:02d}",
                "end_time": f"{end_hh:02d}:{end_mm:02d}"
            })
        return {"itinerary": itinerary}
    else:
        # If the initial order doesn't work, try a different order
        # Let's try meeting Elizabeth first, then Brian, Laura, Jason, Melissa
        s.reset()
        for name in friends:
            friend = friends[name]
            start = meetings[name]['start']
            end = meetings[name]['end']
            s.add(start >= friend['start'])
            s.add(end <= friend['end'])
            s.add(end == start + friend['duration'])

        order = ['Elizabeth', 'Brian', 'Laura', 'Jason', 'Melissa']
        prev_end = current_time
        prev_location = current_location
        for name in order:
            friend = friends[name]
            start = meetings[name]['start']
            end = meetings[name]['end']
            travel_time = travel_times.get((prev_location, friend['location']), 0)
            s.add(start >= prev_end + travel_time)
            prev_end = end
            prev_location = friend['location']

        if s.check() == sat:
            model = s.model()
            itinerary = []
            for name in order:
                start_val = model[meetings[name]['start']].as_long()
                end_val = model[meetings[name]['end']].as_long()
                start_hh = start_val // 60
                start_mm = start_val % 60
                end_hh = end_val // 60
                end_mm = end_val % 60
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{start_hh:02d}:{start_mm:02d}",
                    "end_time": f"{end_hh:02d}:{end_mm:02d}"
                })
            return {"itinerary": itinerary}
        else:
            return {"itinerary": []}

# Run the solver and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))