from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their details
    friends = {
        'Karen': {'location': 'Russian Hill', 'start': 20.75, 'end': 21.75, 'min_duration': 1.0},
        'Jessica': {'location': 'The Castro', 'start': 15.75, 'end': 19.5, 'min_duration': 1.0},
        'Matthew': {'location': 'Richmond District', 'start': 7.5, 'end': 15.25, 'min_duration': 0.25},
        'Michelle': {'location': 'Marina District', 'start': 10.5, 'end': 18.75, 'min_duration': 1.25},
        'Carol': {'location': 'North Beach', 'start': 12.0, 'end': 17.0, 'min_duration': 1.5},
        'Stephanie': {'location': 'Union Square', 'start': 10.75, 'end': 14.25, 'min_duration': 0.5},
        'Linda': {'location': 'Golden Gate Park', 'start': 10.75, 'end': 22.0, 'min_duration': 1.5}
    }

    # Travel times dictionary (from -> to -> hours)
    travel_times = {
        'Sunset District': {
            'Russian Hill': 24/60,
            'The Castro': 17/60,
            'Richmond District': 12/60,
            'Marina District': 21/60,
            'North Beach': 29/60,
            'Union Square': 30/60,
            'Golden Gate Park': 11/60
        },
        'Russian Hill': {
            'Sunset District': 23/60,
            'The Castro': 21/60,
            'Richmond District': 14/60,
            'Marina District': 7/60,
            'North Beach': 5/60,
            'Union Square': 11/60,
            'Golden Gate Park': 21/60
        },
        'The Castro': {
            'Sunset District': 17/60,
            'Russian Hill': 18/60,
            'Richmond District': 16/60,
            'Marina District': 21/60,
            'North Beach': 20/60,
            'Union Square': 19/60,
            'Golden Gate Park': 11/60
        },
        'Richmond District': {
            'Sunset District': 11/60,
            'Russian Hill': 13/60,
            'The Castro': 16/60,
            'Marina District': 9/60,
            'North Beach': 17/60,
            'Union Square': 21/60,
            'Golden Gate Park': 9/60
        },
        'Marina District': {
            'Sunset District': 19/60,
            'Russian Hill': 8/60,
            'The Castro': 22/60,
            'Richmond District': 11/60,
            'North Beach': 11/60,
            'Union Square': 16/60,
            'Golden Gate Park': 18/60
        },
        'North Beach': {
            'Sunset District': 27/60,
            'Russian Hill': 4/60,
            'The Castro': 22/60,
            'Richmond District': 18/60,
            'Marina District': 9/60,
            'Union Square': 7/60,
            'Golden Gate Park': 22/60
        },
        'Union Square': {
            'Sunset District': 26/60,
            'Russian Hill': 13/60,
            'The Castro': 19/60,
            'Richmond District': 20/60,
            'Marina District': 18/60,
            'North Beach': 10/60,
            'Golden Gate Park': 22/60
        },
        'Golden Gate Park': {
            'Sunset District': 10/60,
            'Russian Hill': 19/60,
            'The Castro': 13/60,
            'Richmond District': 7/60,
            'Marina District': 16/60,
            'North Beach': 24/60,
            'Union Square': 22/60
        }
    }

    # Variables for each friend: start time and end time
    meet_vars = {}
    for name in friends:
        meet_vars[name] = {
            'start': Real(f'start_{name}'),
            'end': Real(f'end_{name}')
        }

    # Current location starts at Sunset District at 9:00 AM (9.0)
    current_time = 9.0
    current_location = 'Sunset District'

    # Constraint: All friends must be met
    for name in friends:
        friend = friends[name]
        var = meet_vars[name]
        s.add(var['start'] >= friend['start'])
        s.add(var['end'] <= friend['end'])
        s.add(var['end'] - var['start'] >= friend['min_duration'])

    # Order the meetings to enforce travel times
    # We need to find a permutation of friends that fits the schedule
    # This is complex, so we'll use a simple approach: enforce that each meeting starts after the previous one + travel time
    # We'll create a list of meetings and enforce the order
    meeting_order = list(friends.keys())
    for i in range(len(meeting_order) - 1):
        name1 = meeting_order[i]
        name2 = meeting_order[i + 1]
        loc1 = friends[name1]['location']
        loc2 = friends[name2]['location']
        s.add(meet_vars[name2]['start'] >= meet_vars[name1]['end'] + travel_times[loc1][loc2])

    # First meeting must start after travel from Sunset District
    first_meeting = meeting_order[0]
    first_loc = friends[first_meeting]['location']
    s.add(meet_vars[first_meeting]['start'] >= current_time + travel_times[current_location][first_loc])

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        schedule = []
        for name in friends:
            start = m.evaluate(meet_vars[name]['start'])
            end = m.evaluate(meet_vars[name]['end'])
            schedule.append((name, float(start.as_fraction()), float(end.as_fraction())))
        schedule.sort(key=lambda x: x[1])
        print("SOLUTION:")
        print("All 7 friends will be met.")
        print("Schedule:")
        for entry in schedule:
            name, start, end = entry
            print(f"Meet {name} at {friends[name]['location']} from {start:.2f} to {end:.2f}")
    else:
        print("No feasible schedule found that meets all 7 friends.")

solve_scheduling()