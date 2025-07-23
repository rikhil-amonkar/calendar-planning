from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since midnight
    def time_to_minutes(h, m):
        return h * 60 + m

    # Friends' availability and constraints
    friends = {
        'Emily': {'location': 'Richmond District', 'start': time_to_minutes(19, 0), 'end': time_to_minutes(21, 0), 'min_duration': 15},
        'Margaret': {'location': 'Financial District', 'start': time_to_minutes(16, 30), 'end': time_to_minutes(20, 15), 'min_duration': 75},
        'Ronald': {'location': 'North Beach', 'start': time_to_minutes(18, 30), 'end': time_to_minutes(19, 30), 'min_duration': 45},
        'Deborah': {'location': 'The Castro', 'start': time_to_minutes(13, 45), 'end': time_to_minutes(21, 15), 'min_duration': 90},
        'Jeffrey': {'location': 'Golden Gate Park', 'start': time_to_minutes(11, 15), 'end': time_to_minutes(14, 30), 'min_duration': 120}
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        'Nob Hill': {
            'Richmond District': 14,
            'Financial District': 9,
            'North Beach': 8,
            'The Castro': 17,
            'Golden Gate Park': 17
        },
        'Richmond District': {
            'Nob Hill': 17,
            'Financial District': 22,
            'North Beach': 17,
            'The Castro': 16,
            'Golden Gate Park': 9
        },
        'Financial District': {
            'Nob Hill': 8,
            'Richmond District': 21,
            'North Beach': 7,
            'The Castro': 23,
            'Golden Gate Park': 23
        },
        'North Beach': {
            'Nob Hill': 7,
            'Richmond District': 18,
            'Financial District': 8,
            'The Castro': 22,
            'Golden Gate Park': 22
        },
        'The Castro': {
            'Nob Hill': 16,
            'Richmond District': 16,
            'Financial District': 20,
            'North Beach': 20,
            'Golden Gate Park': 11
        },
        'Golden Gate Park': {
            'Nob Hill': 20,
            'Richmond District': 7,
            'Financial District': 26,
            'North Beach': 24,
            'The Castro': 13
        }
    }

    # Start and end times for each friend's meeting
    start_times = {name: Int(f"start_{name}") for name in friends}
    end_times = {name: Int(f"end_{name}") for name in friends}

    # Constraints for each friend
    for name in friends:
        info = friends[name]
        s.add(start_times[name] >= info['start'])
        s.add(end_times[name] <= info['end'])
        s.add(end_times[name] == start_times[name] + info['min_duration'])
        # Ensure times are within 24-hour format (0 to 1440 minutes)
        s.add(start_times[name] >= 0)
        s.add(end_times[name] <= 1440)

    # Initial location is Nob Hill at time 540 (9:00 AM)
    current_time = 540
    current_location = 'Nob Hill'

    # Define the order of meetings
    order = ['Jeffrey', 'Deborah', 'Margaret', 'Ronald', 'Emily']

    # Add constraints for travel times between meetings
    for i in range(len(order)):
        name = order[i]
        if i == 0:
            # First meeting: travel from Nob Hill to Jeffrey's location
            travel_time = travel_times[current_location][friends[name]['location']]
            s.add(start_times[name] >= current_time + travel_time)
        else:
            # Subsequent meetings: travel from previous location to current friend's location
            prev_name = order[i-1]
            travel_time = travel_times[friends[prev_name]['location']][friends[name]['location']]
            s.add(start_times[name] >= end_times[prev_name] + travel_time)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        for name in order:
            start = m.evaluate(start_times[name])
            end = m.evaluate(end_times[name])
            # Convert minutes back to HH:MM format
            start_h = start.as_long() // 60
            start_m = start.as_long() % 60
            end_h = end.as_long() // 60
            end_m = end.as_long() % 60
            print(f"Meet {name} at {friends[name]['location']} from {start_h:02d}:{start_m:02d} to {end_h:02d}:{end_m:02d}")
        print("All five friends are met successfully.")
    else:
        print("No feasible schedule found that meets all five friends within valid time ranges.")

solve_scheduling()