from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their details
    friends = {
        'William': {'location': 'Alamo Square', 'start': 15.25, 'end': 17.25, 'min_duration': 1.0},
        'Joshua': {'location': 'Richmond District', 'start': 7.0, 'end': 20.0, 'min_duration': 0.25},
        'Joseph': {'location': 'Financial District', 'start': 11.25, 'end': 13.5, 'min_duration': 0.25},
        'David': {'location': 'Union Square', 'start': 16.75, 'end': 19.25, 'min_duration': 0.75},
        'Brian': {'location': 'Fisherman\'s Wharf', 'start': 13.75, 'end': 20.75, 'min_duration': 1.75},
        'Karen': {'location': 'Marina District', 'start': 11.5, 'end': 18.5, 'min_duration': 0.25},
        'Anthony': {'location': 'Haight-Ashbury', 'start': 7.25, 'end': 10.5, 'min_duration': 0.5},
        'Matthew': {'location': 'Mission District', 'start': 17.25, 'end': 19.25, 'min_duration': 2.0},
        'Helen': {'location': 'Pacific Heights', 'start': 8.0, 'end': 12.0, 'min_duration': 1.25},
        'Jeffrey': {'location': 'Golden Gate Park', 'start': 19.0, 'end': 21.5, 'min_duration': 1.0}
    }

    # Travel times dictionary (simplified for this problem)
    travel_times = {
        ('The Castro', 'Alamo Square'): 8/60,
        ('The Castro', 'Richmond District'): 16/60,
        ('The Castro', 'Financial District'): 21/60,
        ('The Castro', 'Union Square'): 19/60,
        ('The Castro', 'Fisherman\'s Wharf'): 24/60,
        ('The Castro', 'Marina District'): 21/60,
        ('The Castro', 'Haight-Ashbury'): 6/60,
        ('The Castro', 'Mission District'): 7/60,
        ('The Castro', 'Pacific Heights'): 16/60,
        ('The Castro', 'Golden Gate Park'): 11/60,
        ('Alamo Square', 'Richmond District'): 11/60,
        ('Alamo Square', 'Financial District'): 17/60,
        ('Alamo Square', 'Union Square'): 14/60,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19/60,
        ('Alamo Square', 'Marina District'): 15/60,
        ('Alamo Square', 'Haight-Ashbury'): 5/60,
        ('Alamo Square', 'Mission District'): 10/60,
        ('Alamo Square', 'Pacific Heights'): 10/60,
        ('Alamo Square', 'Golden Gate Park'): 9/60,
        ('Richmond District', 'Financial District'): 22/60,
        ('Richmond District', 'Union Square'): 21/60,
        ('Richmond District', 'Fisherman\'s Wharf'): 18/60,
        ('Richmond District', 'Marina District'): 9/60,
        ('Richmond District', 'Haight-Ashbury'): 10/60,
        ('Richmond District', 'Mission District'): 20/60,
        ('Richmond District', 'Pacific Heights'): 10/60,
        ('Richmond District', 'Golden Gate Park'): 9/60,
        ('Financial District', 'Union Square'): 9/60,
        ('Financial District', 'Fisherman\'s Wharf'): 10/60,
        ('Financial District', 'Marina District'): 15/60,
        ('Financial District', 'Haight-Ashbury'): 19/60,
        ('Financial District', 'Mission District'): 17/60,
        ('Financial District', 'Pacific Heights'): 13/60,
        ('Financial District', 'Golden Gate Park'): 23/60,
        ('Union Square', 'Fisherman\'s Wharf'): 15/60,
        ('Union Square', 'Marina District'): 18/60,
        ('Union Square', 'Haight-Ashbury'): 18/60,
        ('Union Square', 'Mission District'): 14/60,
        ('Union Square', 'Pacific Heights'): 15/60,
        ('Union Square', 'Golden Gate Park'): 22/60,
        ('Fisherman\'s Wharf', 'Marina District'): 9/60,
        ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22/60,
        ('Fisherman\'s Wharf', 'Mission District'): 22/60,
        ('Fisherman\'s Wharf', 'Pacific Heights'): 12/60,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25/60,
        ('Marina District', 'Haight-Ashbury'): 16/60,
        ('Marina District', 'Mission District'): 20/60,
        ('Marina District', 'Pacific Heights'): 7/60,
        ('Marina District', 'Golden Gate Park'): 18/60,
        ('Haight-Ashbury', 'Mission District'): 11/60,
        ('Haight-Ashbury', 'Pacific Heights'): 12/60,
        ('Haight-Ashbury', 'Golden Gate Park'): 7/60,
        ('Mission District', 'Pacific Heights'): 16/60,
        ('Mission District', 'Golden Gate Park'): 17/60,
        ('Pacific Heights', 'Golden Gate Park'): 16/60
    }

    # Create variables for each friend's meeting start and end times
    start_vars = {}
    end_vars = {}
    for name in friends:
        start_vars[name] = Real(f'start_{name}')
        end_vars[name] = Real(f'end_{name}')

    # Constraints for each friend's meeting time within their availability
    for name in friends:
        friend = friends[name]
        s.add(start_vars[name] >= friend['start'])
        s.add(end_vars[name] <= friend['end'])
        s.add(end_vars[name] - start_vars[name] >= friend['min_duration'])

    # Variables to track whether a friend is met (binary)
    met = {name: Bool(f'met_{name}') for name in friends}
    for name in friends:
        s.add(Implies(met[name], start_vars[name] < end_vars[name]))  # If met, start < end
        s.add(Implies(Not(met[name]), start_vars[name] == end_vars[name]))  # If not met, start == end

    # Current location starts at The Castro at 9.0
    current_time = 9.0
    current_location = 'The Castro'

    # To model the sequence, we need to decide the order of meetings. This is complex, so we'll
    # use a simplified approach where we pick a subset of friends and order them, ensuring travel times.

    # Alternative approach: for each possible permutation of friends, add constraints.
    # But this is computationally expensive. Instead, we'll use a greedy approach in Z3 by allowing any order but ensuring no overlaps.

    # For all pairs of friends, if both are met, then one must be before or after the other with travel time.
    for name1 in friends:
        for name2 in friends:
            if name1 == name2:
                continue
            # If both are met, then either name1 is before name2 or vice versa
            loc1 = friends[name1]['location']
            loc2 = friends[name2]['location']
            travel_time = travel_times.get((loc1, loc2), 0)  # Default to 0 if same location (shouldn't happen)
            s.add(Implies(And(met[name1], met[name2]),
                          Or(end_vars[name1] + travel_time <= start_vars[name2],
                             end_vars[name2] + travel_time <= start_vars[name1])))

    # Maximize the number of friends met
    total_met = Sum([If(met[name], 1, 0) for name in friends])
    s.maximize(total_met)

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        scheduled = []
        for name in friends:
            if m.evaluate(met[name]):
                start = m.evaluate(start_vars[name])
                end = m.evaluate(end_vars[name])
                duration = float(end.as_fraction()) - float(start.as_fraction())
                print(f"Meet {name} at {friends[name]['location']} from {float(start.as_fraction()):.2f} to {float(end.as_fraction()):.2f} (Duration: {duration:.2f} hours)")
                scheduled.append((float(start.as_fraction()), name))
        # Print in chronological order
        scheduled.sort()
        print("\nChronological Order:")
        for time, name in scheduled:
            start = m.evaluate(start_vars[name])
            end = m.evaluate(end_vars[name])
            print(f"Meet {name} at {friends[name]['location']} from {float(start.as_fraction()):.2f} to {float(end.as_fraction()):.2f}")
    else:
        print("No feasible schedule found.")

solve_scheduling()