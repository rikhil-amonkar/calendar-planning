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

    # Travel times dictionary (from -> to -> minutes)
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

    # Variables for each friend: start time, end time, and whether they are met
    meet_vars = {}
    for name in friends:
        meet_vars[name] = {
            'start': Real(f'start_{name}'),
            'end': Real(f'end_{name}'),
            'met': Bool(f'met_{name}')
        }

    # Current location starts at Sunset District at 9:00 AM (9.0)
    current_time = 9.0
    current_location = 'Sunset District'

    # Track the order of meetings to enforce travel times
    meeting_order = []

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        var = meet_vars[name]
        s.add(Implies(var['met'], var['start'] >= friend['start']))
        s.add(Implies(var['met'], var['end'] <= friend['end']))
        s.add(Implies(var['met'], var['end'] - var['start'] >= friend['min_duration']))

    # Ensure no overlapping meetings and account for travel times
    for i, name1 in enumerate(friends):
        for j, name2 in enumerate(friends):
            if i != j:
                # If both are met, then either name1 is before name2 or vice versa with travel time
                s.add(Implies(
                    And(meet_vars[name1]['met'], meet_vars[name2]['met']),
                    Or(
                        meet_vars[name1]['end'] + travel_times[friends[name1]['location']][friends[name2]['location']] <= meet_vars[name2]['start'],
                        meet_vars[name2]['end'] + travel_times[friends[name2]['location']][friends[name1]['location']] <= meet_vars[name1]['start']
                    )
                ))

    # Initial constraint: first meeting must be after travel from Sunset District
    for name in friends:
        s.add(Implies(
            meet_vars[name]['met'],
            meet_vars[name]['start'] >= current_time + travel_times[current_location][friends[name]['location']]
        ))

    # Maximize the number of friends met
    num_met = Sum([If(meet_vars[name]['met'], 1, 0) for name in friends])
    maximize(s, num_met)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        met_friends = []
        schedule = []
        for name in friends:
            if m.evaluate(meet_vars[name]['met']):
                start = m.evaluate(meet_vars[name]['start'])
                end = m.evaluate(meet_vars[name]['end'])
                met_friends.append(name)
                schedule.append((name, float(start.as_fraction()), float(end.as_fraction())))
        schedule.sort(key=lambda x: x[1])
        print("SOLUTION:")
        print(f"Maximum friends met: {len(met_friends)}")
        print("Schedule:")
        for entry in schedule:
            name, start, end = entry
            print(f"Meet {name} at {friends[name]['location']} from {start:.2f} to {end:.2f}")
    else:
        print("No feasible schedule found.")

def maximize(s, expr):
    # Helper function to maximize an expression
    while True:
        s.push()
        s.add(expr > s.model().evaluate(expr, model_completion=True))
        if s.check() == sat:
            continue
        else:
            s.pop()
            break

solve_scheduling()