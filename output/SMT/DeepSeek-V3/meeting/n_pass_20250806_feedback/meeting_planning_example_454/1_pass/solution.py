from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

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
        s.add(Implies(meeting_vars[name]['met'], 
                      And(meeting_vars[name]['start'] >= data['start'],
                          meeting_vars[name]['end'] <= data['end'],
                          meeting_vars[name]['end'] - meeting_vars[name]['start'] >= data['min_duration'])))

    # Initial location: Presidio at time 0 (9:00 AM)
    current_location = 'Presidio'
    current_time = 0

    # Order of meetings to try (priority to longer meetings)
    meeting_order = ['Daniel', 'Ronald', 'Jessica', 'William', 'Ashley']

    # Track which meetings are scheduled
    scheduled = []

    # Try to schedule meetings in order
    for name in meeting_order:
        if name not in meeting_vars:
            continue
        # Check if meeting is possible
        location = friend_minutes[name]['location']
        travel_time = travel_times.get((current_location, location), 0)
        start_time = current_time + travel_time
        end_time = start_time + friend_minutes[name]['min_duration']
        # Check if meeting fits in friend's availability
        if (start_time >= friend_minutes[name]['start'] and 
            end_time <= friend_minutes[name]['end']):
            scheduled.append({
                'name': name,
                'start': start_time,
                'end': end_time,
                'location': location
            })
            current_location = location
            current_time = end_time

    # If not all meetings are scheduled, try to adjust
    if len(scheduled) < len(meeting_order):
        # Add constraints to ensure travel times are respected
        for i in range(len(scheduled) - 1):
            current = scheduled[i]
            next_ = scheduled[i + 1]
            travel_time = travel_times.get((current['location'], next_['location']), 0)
            s.add(next_['start'] >= current['end'] + travel_time)

    # Maximize the number of friends met
    s.maximize(Sum([If(meeting_vars[name]['met'], 1, 0) for name in friends]))

    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        itinerary = []
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
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))