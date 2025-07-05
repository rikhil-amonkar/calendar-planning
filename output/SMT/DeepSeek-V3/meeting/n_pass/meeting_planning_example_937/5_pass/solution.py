from z3 import *
from itertools import combinations

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define friends and their constraints, sorted by duration (longest first)
    friends = [
        {'name': 'Patricia', 'location': 'Nob Hill', 'start': 15.0, 'end': 19.25, 'duration': 2.0},
        {'name': 'George', 'location': 'The Castro', 'start': 14.25, 'end': 19.0, 'duration': 1.75},
        {'name': 'Kimberly', 'location': 'Alamo Square', 'start': 9.0, 'end': 14.5, 'duration': 1.75},
        {'name': 'Joshua', 'location': 'Financial District', 'start': 14.5, 'end': 17.25, 'duration': 1.5},
        {'name': 'William', 'location': 'Presidio', 'start': 7.0, 'end': 12.75, 'duration': 1.0},
        {'name': 'Mary', 'location': 'Marina District', 'start': 14.75, 'end': 16.75, 'duration': 0.75},
        {'name': 'Ronald', 'location': 'Embarcadero', 'start': 18.25, 'end': 20.75, 'duration': 0.5},
        {'name': 'David', 'location': 'Sunset District', 'start': 9.25, 'end': 22.0, 'duration': 0.25},
        {'name': 'Charles', 'location': 'Richmond District', 'start': 17.25, 'end': 21.0, 'duration': 0.25},
        {'name': 'Kenneth', 'location': 'Union Square', 'start': 21.25, 'end': 21.75, 'duration': 0.25}
    ]

    # Travel times from Russian Hill to each location (in hours)
    travel_times = {
        'Sunset District': 23 / 60,
        'Union Square': 10 / 60,
        'Nob Hill': 5 / 60,
        'Marina District': 7 / 60,
        'Richmond District': 14 / 60,
        'Financial District': 11 / 60,
        'Embarcadero': 8 / 60,
        'The Castro': 21 / 60,
        'Alamo Square': 15 / 60,
        'Presidio': 14 / 60
    }

    # Generate all combinations of 8 friends
    for selected in combinations(friends, 8):
        s = Solver()
        variables = {}
        current_time = Real('current_time')
        s.add(current_time == 9.0)
        current_location = 'Russian Hill'

        # Create variables and constraints for each selected friend
        for friend in selected:
            name = friend['name']
            variables[name] = {
                'start': Real(f'start_{name}'),
                'end': Real(f'end_{name}')
            }
            var = variables[name]
            
            # Basic time constraints
            s.add(var['start'] >= friend['start'])
            s.add(var['end'] <= friend['end'])
            s.add(var['end'] - var['start'] >= friend['duration'])
            
            # Travel time constraint
            if current_location != friend['location']:
                travel_time = travel_times[friend['location']]
                s.add(var['start'] >= current_time + travel_time)
            else:
                s.add(var['start'] >= current_time)
            
            # Update current time and location
            current_time = var['end']
            current_location = friend['location']

        # Check if this combination is feasible
        if s.check() == sat:
            m = s.model()
            schedule = []
            for friend in selected:
                name = friend['name']
                start = m[variables[name]['start']]
                end = m[variables[name]['end']]
                if is_real_value(start) and is_real_value(end):
                    schedule.append({
                        'name': name,
                        'start': float(start.as_fraction()),
                        'end': float(end.as_fraction()),
                        'location': friend['location']
                    })
            # Sort by start time
            schedule.sort(key=lambda x: x['start'])
            return schedule

    return None

def is_real_value(v):
    return isinstance(v, RatNumRef)

def print_schedule(schedule):
    if not schedule:
        print("No valid schedule found.")
        return
    print("Optimal Schedule (Meet exactly 8 friends):")
    for meeting in schedule:
        start_h = int(meeting['start'])
        start_m = int((meeting['start'] - start_h) * 60)
        end_h = int(meeting['end'])
        end_m = int((meeting['end'] - end_h) * 60)
        print(f"Meet {meeting['name']} at {meeting['location']} from {start_h}:{start_m:02d} to {end_h}:{end_m:02d}")

# Solve and print the schedule
schedule = solve_scheduling()
print_schedule(schedule)