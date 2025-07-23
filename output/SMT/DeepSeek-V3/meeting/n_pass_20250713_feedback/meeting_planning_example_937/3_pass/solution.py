from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define friends and their constraints
    friends = {
        'David': {'location': 'Sunset District', 'start': 9.25, 'end': 22.0, 'duration': 0.25},
        'Kenneth': {'location': 'Union Square', 'start': 21.25, 'end': 21.75, 'duration': 0.25},
        'Patricia': {'location': 'Nob Hill', 'start': 15.0, 'end': 19.25, 'duration': 2.0},
        'Mary': {'location': 'Marina District', 'start': 14.75, 'end': 16.75, 'duration': 0.75},
        'Charles': {'location': 'Richmond District', 'start': 17.25, 'end': 21.0, 'duration': 0.25},
        'Joshua': {'location': 'Financial District', 'start': 14.5, 'end': 17.25, 'duration': 1.5},
        'Ronald': {'location': 'Embarcadero', 'start': 18.25, 'end': 20.75, 'duration': 0.5},
        'George': {'location': 'The Castro', 'start': 14.25, 'end': 19.0, 'duration': 1.75},
        'Kimberly': {'location': 'Alamo Square', 'start': 9.0, 'end': 14.5, 'duration': 1.75},
        'William': {'location': 'Presidio', 'start': 7.0, 'end': 12.75, 'duration': 1.0}
    }

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

    # Variables for each friend: start and end times of meeting, and a flag indicating if the friend is met
    variables = {}
    for name in friends:
        variables[name] = {
            'start': Real(f'start_{name}'),
            'end': Real(f'end_{name}'),
            'met': Bool(f'met_{name}')
        }

    # Current location starts at Russian Hill at 9:00 AM (9.0)
    current_time = Real('current_time')
    s.add(current_time == 9.0)
    current_location = String('current_location')
    s.add(current_location == StringVal('Russian Hill'))

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        var = variables[name]
        # If the friend is met, enforce their constraints
        s.add(Implies(var['met'], var['start'] >= friend['start']))
        s.add(Implies(var['met'], var['end'] <= friend['end']))
        s.add(Implies(var['met'], var['end'] - var['start'] >= friend['duration']))
        # Travel time from current location to friend's location
        travel_time = travel_times.get(friend['location'], 0)
        s.add(Implies(var['met'], var['start'] >= current_time + If(current_location == StringVal(friend['location']), 0, travel_time)))
        # Update current_time and current_location if the friend is met
        next_time = If(var['met'], var['end'], current_time)
        next_location = If(var['met'], StringVal(friend['location']), current_location)
        current_time = next_time
        current_location = next_location

    # Exactly 8 friends must be met
    s.add(Sum([If(var['met'], 1, 0) for var in variables.values()]) == 8)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        schedule = []
        for name in friends:
            if is_true(m[variables[name]['met']]):
                start = m[variables[name]['start']]
                end = m[variables[name]['end']]
                if is_real_value(start) and is_real_value(end):
                    schedule.append((name, float(start.as_fraction()), float(end.as_fraction())))
        schedule.sort(key=lambda x: x[1])  # Sort by start time
        return schedule
    else:
        return None

def is_real_value(v):
    return isinstance(v, RatNumRef)

def is_true(v):
    return isinstance(v, BoolRef) and v.sexpr() == "true"

def print_schedule(schedule):
    if not schedule:
        print("No valid schedule found.")
        return
    print("Optimal Schedule (Meet exactly 8 friends):")
    for name, start, end in schedule:
        start_str = f"{int(start)}:{int((start - int(start)) * 60):02d}"
        end_str = f"{int(end)}:{int((end - int(end)) * 60):02d}"
        print(f"Meet {name} from {start_str} to {end_str}")

# Solve and print the schedule
schedule = solve_scheduling()
print_schedule(schedule)