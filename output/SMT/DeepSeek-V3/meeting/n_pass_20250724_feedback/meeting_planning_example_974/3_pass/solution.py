from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Define travel times between districts (in minutes)
    travel_times = {
        ('Sunset District', 'Presidio'): 16,
        ('Sunset District', 'Nob Hill'): 27,
        ('Sunset District', 'Pacific Heights'): 21,
        ('Sunset District', 'Mission District'): 25,
        ('Sunset District', 'Marina District'): 21,
        ('Sunset District', 'North Beach'): 28,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'Richmond District'): 12,
        ('Sunset District', 'Embarcadero'): 30,
        ('Sunset District', 'Alamo Square'): 17,
        ('Presidio', 'Sunset District'): 15,
        ('Presidio', 'Nob Hill'): 18,
        ('Presidio', 'Pacific Heights'): 11,
        ('Presidio', 'Mission District'): 26,
        ('Presidio', 'Marina District'): 11,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Russian Hill'): 14,
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'Embarcadero'): 20,
        ('Presidio', 'Alamo Square'): 19,
        ('Nob Hill', 'Sunset District'): 24,
        ('Nob Hill', 'Presidio'): 17,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'Mission District'): 13,
        ('Nob Hill', 'Marina District'): 11,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'Richmond District'): 14,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Nob Hill', 'Alamo Square'): 11,
        ('Pacific Heights', 'Sunset District'): 21,
        ('Pacific Heights', 'Presidio'): 11,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Marina District'): 6,
        ('Pacific Heights', 'North Beach'): 9,
        ('Pacific Heights', 'Russian Hill'): 7,
        ('Pacific Heights', 'Richmond District'): 12,
        ('Pacific Heights', 'Embarcadero'): 10,
        ('Pacific Heights', 'Alamo Square'): 10,
        ('Mission District', 'Sunset District'): 24,
        ('Mission District', 'Presidio'): 25,
        ('Mission District', 'Nob Hill'): 12,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Marina District'): 19,
        ('Mission District', 'North Beach'): 17,
        ('Mission District', 'Russian Hill'): 15,
        ('Mission District', 'Richmond District'): 20,
        ('Mission District', 'Embarcadero'): 19,
        ('Mission District', 'Alamo Square'): 11,
        ('Marina District', 'Sunset District'): 19,
        ('Marina District', 'Presidio'): 10,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Pacific Heights'): 7,
        ('Marina District', 'Mission District'): 20,
        ('Marina District', 'North Beach'): 11,
        ('Marina District', 'Russian Hill'): 8,
        ('Marina District', 'Richmond District'): 11,
        ('Marina District', 'Embarcadero'): 14,
        ('Marina District', 'Alamo Square'): 15,
        ('North Beach', 'Sunset District'): 27,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Pacific Heights'): 8,
        ('North Beach', 'Mission District'): 18,
        ('North Beach', 'Marina District'): 9,
        ('North Beach', 'Russian Hill'): 4,
        ('North Beach', 'Richmond District'): 18,
        ('North Beach', 'Embarcadero'): 6,
        ('North Beach', 'Alamo Square'): 16,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'Pacific Heights'): 7,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', 'Marina District'): 7,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Richmond District'): 14,
        ('Russian Hill', 'Embarcadero'): 8,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Richmond District', 'Sunset District'): 11,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'Nob Hill'): 17,
        ('Richmond District', 'Pacific Heights'): 10,
        ('Richmond District', 'Mission District'): 20,
        ('Richmond District', 'Marina District'): 9,
        ('Richmond District', 'North Beach'): 17,
        ('Richmond District', 'Russian Hill'): 13,
        ('Richmond District', 'Embarcadero'): 19,
        ('Richmond District', 'Alamo Square'): 13,
        ('Embarcadero', 'Sunset District'): 30,
        ('Embarcadero', 'Presidio'): 20,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Pacific Heights'): 11,
        ('Embarcadero', 'Mission District'): 20,
        ('Embarcadero', 'Marina District'): 12,
        ('Embarcadero', 'North Beach'): 5,
        ('Embarcadero', 'Russian Hill'): 8,
        ('Embarcadero', 'Richmond District'): 21,
        ('Embarcadero', 'Alamo Square'): 19,
        ('Alamo Square', 'Sunset District'): 16,
        ('Alamo Square', 'Presidio'): 17,
        ('Alamo Square', 'Nob Hill'): 11,
        ('Alamo Square', 'Pacific Heights'): 10,
        ('Alamo Square', 'Mission District'): 10,
        ('Alamo Square', 'Marina District'): 15,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'Richmond District'): 11,
        ('Alamo Square', 'Embarcadero'): 16,
    }

    # Define friends and their availability
    friends = {
        'Charles': {'location': 'Presidio', 'start': 13.25, 'end': 15.0, 'duration': 105},
        'Robert': {'location': 'Nob Hill', 'start': 13.25, 'end': 17.5, 'duration': 90},
        'Nancy': {'location': 'Pacific Heights', 'start': 14.75, 'end': 22.0, 'duration': 105},
        'Brian': {'location': 'Mission District', 'start': 15.5, 'end': 22.0, 'duration': 60},
        'Kimberly': {'location': 'Marina District', 'start': 17.0, 'end': 19.75, 'duration': 75},
        'David': {'location': 'North Beach', 'start': 14.75, 'end': 16.5, 'duration': 75},
        'William': {'location': 'Russian Hill', 'start': 12.5, 'end': 19.25, 'duration': 120},
        'Jeffrey': {'location': 'Richmond District', 'start': 12.0, 'end': 19.25, 'duration': 45},
        'Karen': {'location': 'Embarcadero', 'start': 14.25, 'end': 20.75, 'duration': 60},
        'Joshua': {'location': 'Alamo Square', 'start': 18.75, 'end': 22.0, 'duration': 60},
    }

    # Convert time to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time):
        hours = int(time)
        minutes = int((time - hours) * 60)
        return hours * 60 + minutes - 540  # Subtract 9:00 AM (540 minutes)

    # Create variables for each meeting
    meeting_vars = {}
    for name in friends:
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        meeting_vars[name] = {'start': start_var, 'end': end_var}

    # Track current location and time
    current_location = 'Sunset District'
    current_time = 0  # Starting at 9:00 AM (0 minutes)

    # Create a list to track meeting order
    meeting_order = []

    # Add constraints for each meeting
    for name in friends:
        friend = friends[name]
        start = meeting_vars[name]['start']
        end = meeting_vars[name]['end']
        duration = friend['duration']
        location = friend['location']

        # Meeting must occur within friend's availability
        opt.add(start >= time_to_minutes(friend['start']))
        opt.add(end <= time_to_minutes(friend['end']))
        opt.add(end == start + duration)

        # Travel time from current location
        travel_time = travel_times.get((current_location, location), 0)
        opt.add(start >= current_time + travel_time)

        # Update current location and time after meeting
        current_location = location
        current_time = end
        meeting_order.append(name)

    # Ensure meetings don't overlap (alternative approach)
    for i in range(len(meeting_order)-1):
        name1 = meeting_order[i]
        name2 = meeting_order[i+1]
        opt.add(meeting_vars[name1]['end'] <= meeting_vars[name2]['start'])

    # Maximize number of friends met
    opt.maximize(Sum([If(meeting_vars[name]['start'] >= 0, 1, 0) for name in friends]))

    # Check for solution
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for name in friends:
            start_val = m[meeting_vars[name]['start']].as_long()
            if start_val >= 0:  # Only include scheduled meetings
                end_val = m[meeting_vars[name]['end']].as_long()
                # Convert back to HH:MM format
                start_hour = 9 + (start_val) // 60
                start_minute = (start_val) % 60
                end_hour = 9 + (end_val) // 60
                end_minute = (end_val) % 60
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{start_hour:02d}:{start_minute:02d}",
                    "end_time": f"{end_hour:02d}:{end_minute:02d}"
                })
        # Sort by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print solution
solution = solve_scheduling()
print("SOLUTION:")
print(json.dumps(solution, indent=2))