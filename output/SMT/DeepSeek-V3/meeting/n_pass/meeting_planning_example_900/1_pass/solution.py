from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the friends and their details
    friends = {
        'Matthew': {'location': 'The Castro', 'start': 16.5, 'end': 20.0, 'min_duration': 0.75},
        'Rebecca': {'location': 'Nob Hill', 'start': 15.25, 'end': 19.25, 'min_duration': 1.75},
        'Brian': {'location': 'Marina District', 'start': 14.25, 'end': 22.0, 'min_duration': 0.5},
        'Emily': {'location': 'Pacific Heights', 'start': 11.25, 'end': 19.75, 'min_duration': 0.25},
        'Karen': {'location': 'Haight-Ashbury', 'start': 11.75, 'end': 17.5, 'min_duration': 0.5},
        'Stephanie': {'location': 'Mission District', 'start': 13.0, 'end': 15.75, 'min_duration': 1.25},
        'James': {'location': 'Chinatown', 'start': 14.5, 'end': 19.0, 'min_duration': 2.0},
        'Steven': {'location': 'Russian Hill', 'start': 14.0, 'end': 20.0, 'min_duration': 0.5},
        'Elizabeth': {'location': 'Alamo Square', 'start': 13.0, 'end': 17.25, 'min_duration': 2.0},
        'William': {'location': 'Bayview', 'start': 18.25, 'end': 20.25, 'min_duration': 1.5}
    }

    # Travel times (simplified as a dictionary of dictionaries)
    travel_times = {
        'Richmond District': {
            'The Castro': 16/60, 'Nob Hill': 17/60, 'Marina District': 9/60,
            'Pacific Heights': 10/60, 'Haight-Ashbury': 10/60, 'Mission District': 20/60,
            'Chinatown': 20/60, 'Russian Hill': 13/60, 'Alamo Square': 13/60, 'Bayview': 27/60
        },
        'The Castro': {
            'Richmond District': 16/60, 'Nob Hill': 16/60, 'Marina District': 21/60,
            'Pacific Heights': 16/60, 'Haight-Ashbury': 6/60, 'Mission District': 7/60,
            'Chinatown': 22/60, 'Russian Hill': 18/60, 'Alamo Square': 8/60, 'Bayview': 19/60
        },
        'Nob Hill': {
            'Richmond District': 14/60, 'The Castro': 17/60, 'Marina District': 11/60,
            'Pacific Heights': 8/60, 'Haight-Ashbury': 13/60, 'Mission District': 13/60,
            'Chinatown': 6/60, 'Russian Hill': 5/60, 'Alamo Square': 11/60, 'Bayview': 19/60
        },
        'Marina District': {
            'Richmond District': 11/60, 'The Castro': 22/60, 'Nob Hill': 12/60,
            'Pacific Heights': 7/60, 'Haight-Ashbury': 16/60, 'Mission District': 20/60,
            'Chinatown': 15/60, 'Russian Hill': 8/60, 'Alamo Square': 15/60, 'Bayview': 27/60
        },
        'Pacific Heights': {
            'Richmond District': 12/60, 'The Castro': 16/60, 'Nob Hill': 8/60,
            'Marina District': 6/60, 'Haight-Ashbury': 11/60, 'Mission District': 15/60,
            'Chinatown': 11/60, 'Russian Hill': 7/60, 'Alamo Square': 10/60, 'Bayview': 22/60
        },
        'Haight-Ashbury': {
            'Richmond District': 10/60, 'The Castro': 6/60, 'Nob Hill': 15/60,
            'Marina District': 17/60, 'Pacific Heights': 12/60, 'Mission District': 11/60,
            'Chinatown': 19/60, 'Russian Hill': 17/60, 'Alamo Square': 5/60, 'Bayview': 18/60
        },
        'Mission District': {
            'Richmond District': 20/60, 'The Castro': 7/60, 'Nob Hill': 12/60,
            'Marina District': 19/60, 'Pacific Heights': 16/60, 'Haight-Ashbury': 12/60,
            'Chinatown': 16/60, 'Russian Hill': 15/60, 'Alamo Square': 11/60, 'Bayview': 14/60
        },
        'Chinatown': {
            'Richmond District': 20/60, 'The Castro': 22/60, 'Nob Hill': 9/60,
            'Marina District': 12/60, 'Pacific Heights': 10/60, 'Haight-Ashbury': 19/60,
            'Mission District': 17/60, 'Russian Hill': 7/60, 'Alamo Square': 17/60, 'Bayview': 20/60
        },
        'Russian Hill': {
            'Richmond District': 14/60, 'The Castro': 21/60, 'Nob Hill': 5/60,
            'Marina District': 7/60, 'Pacific Heights': 7/60, 'Haight-Ashbury': 17/60,
            'Mission District': 16/60, 'Chinatown': 9/60, 'Alamo Square': 15/60, 'Bayview': 23/60
        },
        'Alamo Square': {
            'Richmond District': 11/60, 'The Castro': 8/60, 'Nob Hill': 11/60,
            'Marina District': 15/60, 'Pacific Heights': 10/60, 'Haight-Ashbury': 5/60,
            'Mission District': 10/60, 'Chinatown': 15/60, 'Russian Hill': 13/60, 'Bayview': 16/60
        },
        'Bayview': {
            'Richmond District': 25/60, 'The Castro': 19/60, 'Nob Hill': 20/60,
            'Marina District': 27/60, 'Pacific Heights': 23/60, 'Haight-Ashbury': 19/60,
            'Mission District': 13/60, 'Chinatown': 19/60, 'Russian Hill': 23/60, 'Alamo Square': 16/60
        }
    }

    # Create variables for each friend's meeting start and end times
    meeting_starts = {name: Real(f'start_{name}') for name in friends}
    meeting_ends = {name: Real(f'end_{name}') for name in friends}
    meet = {name: Bool(f'meet_{name}') for name in friends}  # Whether to meet the friend or not

    # Current location starts at Richmond District at 9:00 AM (9.0)
    current_time = Real('current_time')
    s.add(current_time == 9.0)
    current_location = 'Richmond District'

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        loc = friend['location']
        start = friend['start']
        end = friend['end']
        min_duration = friend['min_duration']

        # If we meet the friend, their meeting must be within their availability
        s.add(Implies(meet[name], And(
            meeting_starts[name] >= start,
            meeting_ends[name] <= end,
            meeting_ends[name] - meeting_starts[name] >= min_duration
        )))

        # If we don't meet the friend, their start and end times are unconstrained
        s.add(Implies(Not(meet[name]), And(
            meeting_starts[name] == 0,
            meeting_ends[name] == 0
        )))

    # Ensure no overlapping meetings and account for travel time
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                loc1 = friends[name1]['location']
                loc2 = friends[name2]['location']
                travel_time = travel_times[loc1][loc2]

                # If both meetings are scheduled, they must not overlap and have travel time between
                s.add(Implies(And(meet[name1], meet[name2]),
                      Or(
                          meeting_ends[name1] + travel_time <= meeting_starts[name2],
                          meeting_ends[name2] + travel_time <= meeting_starts[name1]
                      ))

    # The first meeting must be after the current time plus travel time from Richmond District
    for name in friends:
        loc = friends[name]['location']
        travel_time = travel_times[current_location][loc]
        s.add(Implies(meet[name], meeting_starts[name] >= current_time + travel_time))

    # Maximize the number of friends met
    num_met = Sum([If(meet[name], 1, 0) for name in friends])
    s.maximize(num_met)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        print(f"Total friends met: {m.evaluate(num_met)}")
        print("\nMeetings:")
        for name in sorted(friends.keys(), key=lambda x: m.evaluate(meeting_starts[x]).as_fraction()):
            if m.evaluate(meet[name]):
                start = m.evaluate(meeting_starts[name])
                end = m.evaluate(meeting_ends[name])
                duration = end - start
                print(f"{name}: {start} to {end} (duration: {duration}) at {friends[name]['location']}")
    else:
        print("No feasible schedule found.")

solve_scheduling()