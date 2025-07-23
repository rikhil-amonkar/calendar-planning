from z3 import *
import itertools

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

    # Generate all possible combinations of 8 friends
    friend_names = list(friends.keys())
    for selected in itertools.combinations(friend_names, 8):
        s = Solver()
        variables = {}
        current_time = Real('current_time')
        s.add(current_time == 9.0)
        current_location = 'Russian Hill'

        # Variables for each selected friend
        for name in selected:
            variables[name] = {
                'start': Real(f'start_{name}'),
                'end': Real(f'end_{name}')
            }
            friend = friends[name]
            var = variables[name]
            s.add(var['start'] >= friend['start'])
            s.add(var['end'] <= friend['end'])
            s.add(var['end'] - var['start'] >= friend['duration'])
            # Travel time
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
            for name in selected:
                start = m[variables[name]['start']]
                end = m[variables[name]['end']]
                if is_real_value(start) and is_real_value(end):
                    schedule.append((name, float(start.as_fraction()), float(end.as_fraction())))
            schedule.sort(key=lambda x: x[1])
            return schedule

    return None

def is_real_value(v):
    return isinstance(v, RatNumRef)

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