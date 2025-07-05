from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define friends and their details
    friends = {
        'Amanda': {'location': 'Marina District', 'start': 14.75, 'end': 19.5, 'min_duration': 105/60},
        'Melissa': {'location': 'The Castro', 'start': 9.5, 'end': 17.0, 'min_duration': 0.5},
        'Jeffrey': {'location': 'Fisherman\'s Wharf', 'start': 12.75, 'end': 18.75, 'min_duration': 2.0},
        'Matthew': {'location': 'Bayview', 'start': 10.25, 'end': 13.25, 'min_duration': 0.5},
        'Nancy': {'location': 'Pacific Heights', 'start': 17.0, 'end': 21.5, 'min_duration': 105/60},
        'Karen': {'location': 'Mission District', 'start': 17.5, 'end': 20.5, 'min_duration': 105/60},
        'Robert': {'location': 'Alamo Square', 'start': 11.25, 'end': 17.5, 'min_duration': 2.0},
        'Joseph': {'location': 'Golden Gate Park', 'start': 8.5, 'end': 21.25, 'min_duration': 105/60}
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        'Presidio': {
            'Marina District': 11/60,
            'The Castro': 21/60,
            'Fisherman\'s Wharf': 19/60,
            'Bayview': 31/60,
            'Pacific Heights': 11/60,
            'Mission District': 26/60,
            'Alamo Square': 19/60,
            'Golden Gate Park': 12/60
        },
        'Marina District': {
            'Presidio': 10/60,
            'The Castro': 22/60,
            'Fisherman\'s Wharf': 10/60,
            'Bayview': 27/60,
            'Pacific Heights': 7/60,
            'Mission District': 20/60,
            'Alamo Square': 15/60,
            'Golden Gate Park': 18/60
        },
        'The Castro': {
            'Presidio': 20/60,
            'Marina District': 21/60,
            'Fisherman\'s Wharf': 24/60,
            'Bayview': 19/60,
            'Pacific Heights': 16/60,
            'Mission District': 7/60,
            'Alamo Square': 8/60,
            'Golden Gate Park': 11/60
        },
        'Fisherman\'s Wharf': {
            'Presidio': 17/60,
            'Marina District': 9/60,
            'The Castro': 27/60,
            'Bayview': 26/60,
            'Pacific Heights': 12/60,
            'Mission District': 22/60,
            'Alamo Square': 21/60,
            'Golden Gate Park': 25/60
        },
        'Bayview': {
            'Presidio': 32/60,
            'Marina District': 27/60,
            'The Castro': 19/60,
            'Fisherman\'s Wharf': 25/60,
            'Pacific Heights': 23/60,
            'Mission District': 13/60,
            'Alamo Square': 16/60,
            'Golden Gate Park': 22/60
        },
        'Pacific Heights': {
            'Presidio': 11/60,
            'Marina District': 6/60,
            'The Castro': 16/60,
            'Fisherman\'s Wharf': 13/60,
            'Bayview': 22/60,
            'Mission District': 15/60,
            'Alamo Square': 10/60,
            'Golden Gate Park': 15/60
        },
        'Mission District': {
            'Presidio': 25/60,
            'Marina District': 19/60,
            'The Castro': 7/60,
            'Fisherman\'s Wharf': 22/60,
            'Bayview': 14/60,
            'Pacific Heights': 16/60,
            'Alamo Square': 11/60,
            'Golden Gate Park': 17/60
        },
        'Alamo Square': {
            'Presidio': 17/60,
            'Marina District': 15/60,
            'The Castro': 8/60,
            'Fisherman\'s Wharf': 19/60,
            'Bayview': 16/60,
            'Pacific Heights': 10/60,
            'Mission District': 10/60,
            'Golden Gate Park': 9/60
        },
        'Golden Gate Park': {
            'Presidio': 11/60,
            'Marina District': 16/60,
            'The Castro': 13/60,
            'Fisherman\'s Wharf': 24/60,
            'Bayview': 23/60,
            'Pacific Heights': 16/60,
            'Mission District': 17/60,
            'Alamo Square': 9/60
        }
    }

    # Create variables for each friend's meeting start and end times
    meeting_start = {name: Real(f'start_{name}') for name in friends}
    meeting_end = {name: Real(f'end_{name}') for name in friends}
    meet = {name: Bool(f'meet_{name}') for name in friends}  # Whether to meet the friend

    # Initial constraints: arrival at Presidio at 9:00 AM (9.0 hours)
    current_time = 9.0
    current_location = 'Presidio'

    # Constraints for each friend
    for name in friends:
        info = friends[name]
        # If meeting the friend, the meeting must be within their window and meet duration
        s.add(Implies(meet[name], And(
            meeting_start[name] >= info['start'],
            meeting_end[name] <= info['end'],
            meeting_end[name] - meeting_start[name] >= info['min_duration']
        )))
        # If not meeting the friend, the start and end times are unconstrained (but we can set them to zero)
        s.add(Implies(Not(meet[name]), And(
            meeting_start[name] == 0,
            meeting_end[name] == 0
        )))

    # No overlapping meetings: for any two distinct friends, if both are met, one must be after the other plus travel time
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                loc1 = friends[name1]['location']
                loc2 = friends[name2]['location']
                travel_time = travel_times[loc1][loc2]
                # Either name1's meeting ends before name2's starts minus travel time, or vice versa
                s.add(Implies(And(meet[name1], meet[name2]), Or(
                    meeting_end[name1] + travel_time <= meeting_start[name2],
                    meeting_end[name2] + travel_times[loc2][loc1] <= meeting_start[name1]
                )))

    # Constraint to meet exactly 7 friends
    s.add(Sum([If(meet[name], 1, 0) for name in friends]) == 7

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        scheduled_friends = []
        for name in friends:
            if m.evaluate(meet[name]):
                start = m.evaluate(meeting_start[name])
                end = m.evaluate(meeting_end[name])
                start_val = start.as_fraction() if is_rational_value(start) else float(start.numerator_as_long())/float(start.denominator_as_long())
                end_val = end.as_fraction() if is_rational_value(end) else float(end.numerator_as_long())/float(end.denominator_as_long())
                scheduled_friends.append((name, start_val, end_val))
        # Sort by start time
        scheduled_friends.sort(key=lambda x: x[1])
        for name, start, end in scheduled_friends:
            start_hr = int(start)
            start_min = int((start - start_hr) * 60)
            end_hr = int(end)
            end_min = int((end - end_hr) * 60)
            print(f"Meet {name} at {friends[name]['location']} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}")
        print(f"Total friends met: {len(scheduled_friends)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()