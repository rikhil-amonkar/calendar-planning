from z3 import *

def solve_scheduling():
    s = Solver()

    # Define all possible friends and their locations
    friends = {
        'sarah': {'location': 'Russian Hill', 'window': (435, 570), 'duration': 45},
        'ronald': {'location': 'Nob Hill', 'window': (600, 1020), 'duration': 105},
        'helen': {'location': 'The Castro', 'window': (810, 1020), 'duration': 120},
        'joshua': {'location': 'Sunset District', 'window': (855, 1290), 'duration': 90},
        'margaret': {'location': 'Haight-Ashbury', 'window': (615, 1320), 'duration': 60}
    }

    # Create variables for each friend's meeting times
    for name in friends:
        friends[name]['start'] = Int(f'{name}_start')
        friends[name]['end'] = Int(f'{name}_end')

    # Add basic constraints for each friend
    for name, data in friends.items():
        s.add(data['start'] >= data['window'][0])
        s.add(data['end'] <= data['window'][1])
        s.add(data['end'] - data['start'] >= data['duration'])

    # Travel times between locations (in minutes)
    travel_times = {
        ('Pacific Heights', 'Russian Hill'): 7,
        ('Russian Hill', 'Nob Hill'): 5,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'Sunset District'): 25,
        ('Nob Hill', 'Haight-Ashbury'): 13,
        ('The Castro', 'Sunset District'): 17,
        ('The Castro', 'Haight-Ashbury'): 6,
        ('Sunset District', 'Haight-Ashbury'): 15
    }

    # We need to meet exactly 4 friends
    # Create a variable to track which friend is excluded
    excluded = [Bool(f'exclude_{name}') for name in friends]
    s.add(Sum([If(e, 1, 0) for e in excluded]) == 1)

    # If a friend is excluded, set their times to 0
    for i, name in enumerate(friends):
        s.add(Implies(excluded[i], And(friends[name]['start'] == 0, friends[name]['end'] == 0)))

    # Starting point: Pacific Heights at 9:00 AM (540 minutes)
    current_time = 540

    # Try different meeting orders
    # We'll try all possible sequences of 4 friends
    from itertools import permutations
    for sequence in permutations(friends.keys(), 4):
        temp_s = Solver()
        temp_s.add(s.assertions())

        # Set the excluded friend
        excluded_friend = [name for name in friends if name not in sequence][0]
        temp_s.add(excluded[list(friends.keys()).index(excluded_friend)] == True)

        # Build the schedule for this sequence
        prev_location = 'Pacific Heights'
        prev_end = current_time
        feasible = True

        for name in sequence:
            data = friends[name]
            start = data['start']
            end = data['end']

            # Calculate travel time
            travel_time = travel_times.get((prev_location, data['location']), 0)
            if travel_time == 0:
                feasible = False
                break

            # Add constraints
            temp_s.add(start >= prev_end + travel_time)
            prev_end = end
            prev_location = data['location']

        if not feasible:
            continue

        if temp_s.check() == sat:
            m = temp_s.model()
            print("SOLUTION:")
            for name in sequence:
                start = m[friends[name]['start']].as_long()
                end = m[friends[name]['end']].as_long()
                print(f"Meet {name.capitalize()} at {friends[name]['location']}: from {start} to {end}")
            return

    print("No feasible schedule found.")

solve_scheduling()