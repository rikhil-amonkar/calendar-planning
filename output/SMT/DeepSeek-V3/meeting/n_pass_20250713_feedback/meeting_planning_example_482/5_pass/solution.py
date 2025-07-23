from z3 import *
import itertools

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Locations and friends
    friends = {
        'Stephanie': {'location': 'Mission District', 'start': 8.25, 'end': 13.75, 'duration': 1.5},
        'Sandra': {'location': 'Bayview', 'start': 13.0, 'end': 19.5, 'duration': 0.25},
        'Richard': {'location': 'Pacific Heights', 'start': 7.25, 'end': 10.25, 'duration': 1.25},
        'Brian': {'location': 'Russian Hill', 'start': 12.25, 'end': 16.0, 'duration': 2.0},
        'Jason': {'location': 'Fisherman\'s Wharf', 'start': 8.5, 'end': 17.75, 'duration': 1.0}
    }

    # Travel times (in hours)
    travel_times = {
        ('Haight-Ashbury', 'Mission District'): 11/60,
        ('Haight-Ashbury', 'Bayview'): 18/60,
        ('Haight-Ashbury', 'Pacific Heights'): 12/60,
        ('Haight-Ashbury', 'Russian Hill'): 17/60,
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23/60,
        ('Mission District', 'Haight-Ashbury'): 12/60,
        ('Mission District', 'Bayview'): 15/60,
        ('Mission District', 'Pacific Heights'): 16/60,
        ('Mission District', 'Russian Hill'): 15/60,
        ('Mission District', 'Fisherman\'s Wharf'): 22/60,
        ('Bayview', 'Haight-Ashbury'): 19/60,
        ('Bayview', 'Mission District'): 13/60,
        ('Bayview', 'Pacific Heights'): 23/60,
        ('Bayview', 'Russian Hill'): 23/60,
        ('Bayview', 'Fisherman\'s Wharf'): 25/60,
        ('Pacific Heights', 'Haight-Ashbury'): 11/60,
        ('Pacific Heights', 'Mission District'): 15/60,
        ('Pacific Heights', 'Bayview'): 22/60,
        ('Pacific Heights', 'Russian Hill'): 7/60,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13/60,
        ('Russian Hill', 'Haight-Ashbury'): 17/60,
        ('Russian Hill', 'Mission District'): 16/60,
        ('Russian Hill', 'Bayview'): 23/60,
        ('Russian Hill', 'Pacific Heights'): 7/60,
        ('Russian Hill', 'Fisherman\'s Wharf'): 7/60,
        ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22/60,
        ('Fisherman\'s Wharf', 'Mission District'): 22/60,
        ('Fisherman\'s Wharf', 'Bayview'): 26/60,
        ('Fisherman\'s Wharf', 'Pacific Heights'): 12/60,
        ('Fisherman\'s Wharf', 'Russian Hill'): 7/60
    }

    # Variables for start and end times of each meeting
    meeting_start = {name: Real(f'start_{name}') for name in friends}
    meeting_end = {name: Real(f'end_{name}') for name in friends}

    # Variables to indicate if a friend is met
    meet_friend = {name: Bool(f'meet_{name}') for name in friends}

    # Exactly 4 friends must be met
    s.add(Sum([If(meet_friend[name], 1, 0) for name in friends]) == 4)

    # Current location starts at Haight-Ashbury at 9.0 (9:00 AM)
    current_time = 9.0
    current_location = 'Haight-Ashbury'

    # For each friend, if they are met, enforce their constraints
    for name in friends:
        friend = friends[name]
        s.add(Implies(meet_friend[name], meeting_start[name] >= friend['start']))
        s.add(Implies(meet_friend[name], meeting_end[name] <= friend['end']))
        s.add(Implies(meet_friend[name], meeting_end[name] == meeting_start[name] + friend['duration']))

    # Generate all possible sequences of 4 friends
    friend_names = list(friends.keys())
    for selected_friends in itertools.permutations(friend_names, 4):
        # Reset current time and location
        current_time = 9.0
        current_location = 'Haight-Ashbury'
        temp_solver = Solver()
        temp_solver.add(s.assertions())

        # Enforce the selected sequence
        for i in range(4):
            name = selected_friends[i]
            temp_solver.add(meet_friend[name])
            if i == 0:
                # First meeting: travel from Haight-Ashbury
                travel_time = travel_times[(current_location, friends[name]['location'])]
                temp_solver.add(meeting_start[name] == current_time + travel_time)  # Exact start time
            else:
                # Subsequent meetings: travel from previous location
                prev_name = selected_friends[i-1]
                travel_time = travel_times[(friends[prev_name]['location'], friends[name]['location'])]
                temp_solver.add(meeting_start[name] >= meeting_end[prev_name] + travel_time)

        # Check if this sequence is feasible
        if temp_solver.check() == sat:
            m = temp_solver.model()
            print("SOLUTION:")
            for name in selected_friends:
                start = m[meeting_start[name]].as_fraction()
                end = m[meeting_end[name]].as_fraction()
                print(f"Meet {name} at {friends[name]['location']} from {float(start):.2f} to {float(end):.2f}")
            return

    print("No valid schedule found.")

solve_scheduling()