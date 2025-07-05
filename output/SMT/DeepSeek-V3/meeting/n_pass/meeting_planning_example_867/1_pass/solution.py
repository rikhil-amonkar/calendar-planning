from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Friends and their details
    friends = {
        'Elizabeth': {'location': 'Mission District', 'start': 10.5, 'end': 20.0, 'min_duration': 1.5},
        'David': {'location': 'Union Square', 'start': 15.25, 'end': 19.0, 'min_duration': 0.75},
        'Sandra': {'location': 'Pacific Heights', 'start': 7.0, 'end': 20.0, 'min_duration': 2.0},
        'Thomas': {'location': 'Bayview', 'start': 19.5, 'end': 20.5, 'min_duration': 0.5},
        'Robert': {'location': 'Fisherman\'s Wharf', 'start': 10.0, 'end': 15.0, 'min_duration': 0.25},
        'Kenneth': {'location': 'Marina District', 'start': 10.75, 'end': 13.0, 'min_duration': 0.75},
        'Melissa': {'location': 'Richmond District', 'start': 18.25, 'end': 20.0, 'min_duration': 0.25},
        'Kimberly': {'location': 'Sunset District', 'start': 10.25, 'end': 18.25, 'min_duration': 1.75},
        'Amanda': {'location': 'Golden Gate Park', 'start': 7.75, 'end': 18.75, 'min_duration': 0.25}
    }

    # Travel times (simplified as symmetric for this problem)
    travel_times = {
        ('Haight-Ashbury', 'Mission District'): 11/60,
        ('Haight-Ashbury', 'Union Square'): 19/60,
        ('Haight-Ashbury', 'Pacific Heights'): 12/60,
        ('Haight-Ashbury', 'Bayview'): 18/60,
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23/60,
        ('Haight-Ashbury', 'Marina District'): 17/60,
        ('Haight-Ashbury', 'Richmond District'): 10/60,
        ('Haight-Ashbury', 'Sunset District'): 15/60,
        ('Haight-Ashbury', 'Golden Gate Park'): 7/60,
        ('Mission District', 'Union Square'): 15/60,
        ('Mission District', 'Pacific Heights'): 16/60,
        ('Mission District', 'Bayview'): 14/60,
        ('Mission District', 'Fisherman\'s Wharf'): 22/60,
        ('Mission District', 'Marina District'): 19/60,
        ('Mission District', 'Richmond District'): 20/60,
        ('Mission District', 'Sunset District'): 24/60,
        ('Mission District', 'Golden Gate Park'): 17/60,
        ('Union Square', 'Pacific Heights'): 15/60,
        ('Union Square', 'Bayview'): 15/60,
        ('Union Square', 'Fisherman\'s Wharf'): 15/60,
        ('Union Square', 'Marina District'): 18/60,
        ('Union Square', 'Richmond District'): 20/60,
        ('Union Square', 'Sunset District'): 27/60,
        ('Union Square', 'Golden Gate Park'): 22/60,
        ('Pacific Heights', 'Bayview'): 22/60,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13/60,
        ('Pacific Heights', 'Marina District'): 6/60,
        ('Pacific Heights', 'Richmond District'): 12/60,
        ('Pacific Heights', 'Sunset District'): 21/60,
        ('Pacific Heights', 'Golden Gate Park'): 15/60,
        ('Bayview', 'Fisherman\'s Wharf'): 25/60,
        ('Bayview', 'Marina District'): 27/60,
        ('Bayview', 'Richmond District'): 25/60,
        ('Bayview', 'Sunset District'): 23/60,
        ('Bayview', 'Golden Gate Park'): 22/60,
        ('Fisherman\'s Wharf', 'Marina District'): 9/60,
        ('Fisherman\'s Wharf', 'Richmond District'): 18/60,
        ('Fisherman\'s Wharf', 'Sunset District'): 27/60,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25/60,
        ('Marina District', 'Richmond District'): 11/60,
        ('Marina District', 'Sunset District'): 19/60,
        ('Marina District', 'Golden Gate Park'): 18/60,
        ('Richmond District', 'Sunset District'): 11/60,
        ('Richmond District', 'Golden Gate Park'): 9/60,
        ('Sunset District', 'Golden Gate Park'): 10/60
    }

    # Add symmetric travel times
    for (a, b), time in list(travel_times.items()):
        if (b, a) not in travel_times:
            travel_times[(b, a)] = time

    # Variables for each friend: start and end times, and whether they are met
    meet_vars = {}
    start_vars = {}
    end_vars = {}
    for name in friends:
        meet_vars[name] = Bool(name)
        start_vars[name] = Real(f'start_{name}')
        end_vars[name] = Real(f'end_{name}')

    # Current location starts at Haight-Ashbury at 9.0 (9:00 AM)
    current_location = 'Haight-Ashbury'
    current_time = 9.0

    # Constraints for each friend
    order = []
    for name in friends:
        friend = friends[name]
        s.add(Implies(meet_vars[name], start_vars[name] >= friend['start']))
        s.add(Implies(meet_vars[name], end_vars[name] <= friend['end']))
        s.add(Implies(meet_vars[name], end_vars[name] - start_vars[name] >= friend['min_duration']))
        order.append((name, meet_vars[name], start_vars[name], end_vars[name]))

    # Sequence constraints: if meeting a friend, must have time to travel from previous location
    # We need to model the sequence of meetings
    # This is complex; for simplicity, we'll assume a fixed order and let Z3 handle permutations
    # Alternatively, we can use a graph approach or sequence variables, but that's more involved

    # For simplicity, let's try to meet as many friends as possible without strict ordering
    # We'll add constraints that if two friends are met, their times don't overlap considering travel

    # For all pairs of friends, if both are met, then one must finish before the other starts, plus travel time
    for i, (name1, meet1, start1, end1) in enumerate(order):
        loc1 = friends[name1]['location']
        for j, (name2, meet2, start2, end2) in enumerate(order):
            if i == j:
                continue
            loc2 = friends[name2]['location']
            travel_key = (loc1, loc2)
            if travel_key in travel_times:
                travel_time = travel_times[travel_key]
            else:
                travel_time = travel_times.get((loc2, loc1), 0)  # should not happen as we added symmetric
            s.add(Implies(And(meet1, meet2),
                  Or(end1 + travel_time <= start2, end2 + travel_time <= start1)))

    # Maximize the number of friends met
    total_met = Sum([If(meet_vars[name], 1, 0) for name in friends])
    s.maximize(total_met)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("Optimal schedule:")
        met_friends = []
        for name in friends:
            if m.evaluate(meet_vars[name]):
                start = m.evaluate(start_vars[name])
                end = m.evaluate(end_vars[name])
                start_hour = int(start.as_fraction().numerator / start.as_fraction().denominator)
                start_min = int((start.as_fraction().numerator % start.as_fraction().denominator) * 60 / start.as_fraction().denominator)
                end_hour = int(end.as_fraction().numerator / end.as_fraction().denominator)
                end_min = int((end.as_fraction().numerator % end.as_fraction().denominator) * 60 / end.as_fraction().denominator)
                print(f"Meet {name} at {friends[name]['location']} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}")
                met_friends.append(name)
        print(f"Total friends met: {len(met_friends)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()