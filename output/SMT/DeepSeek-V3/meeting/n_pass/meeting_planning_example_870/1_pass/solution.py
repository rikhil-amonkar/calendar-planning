from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Friends and their details
    friends = {
        'Linda': {'location': 'Marina District', 'start': 18*60, 'end': 22*60, 'duration': 30},
        'Kenneth': {'location': 'The Castro', 'start': 14*60 + 45, 'end': 16*60 + 15, 'duration': 30},
        'Kimberly': {'location': 'Richmond District', 'start': 14*60 + 15, 'end': 22*60, 'duration': 30},
        'Paul': {'location': 'Alamo Square', 'start': 21*60, 'end': 21*60 + 30, 'duration': 15},
        'Carol': {'location': 'Financial District', 'start': 10*60 + 15, 'end': 12*60, 'duration': 60},
        'Brian': {'location': 'Presidio', 'start': 10*60, 'end': 21*60 + 30, 'duration': 75},
        'Laura': {'location': 'Mission District', 'start': 16*60 + 15, 'end': 20*60 + 30, 'duration': 30},
        'Sandra': {'location': 'Nob Hill', 'start': 9*60 + 15, 'end': 18*60 + 30, 'duration': 60},
        'Karen': {'location': 'Russian Hill', 'start': 18*60 + 30, 'end': 22*60, 'duration': 75}
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        'Pacific Heights': {
            'Marina District': 6,
            'The Castro': 16,
            'Richmond District': 12,
            'Alamo Square': 10,
            'Financial District': 13,
            'Presidio': 11,
            'Mission District': 15,
            'Nob Hill': 8,
            'Russian Hill': 7
        },
        'Marina District': {
            'Pacific Heights': 7,
            'The Castro': 22,
            'Richmond District': 11,
            'Alamo Square': 15,
            'Financial District': 17,
            'Presidio': 10,
            'Mission District': 20,
            'Nob Hill': 12,
            'Russian Hill': 8
        },
        'The Castro': {
            'Pacific Heights': 16,
            'Marina District': 21,
            'Richmond District': 16,
            'Alamo Square': 8,
            'Financial District': 21,
            'Presidio': 20,
            'Mission District': 7,
            'Nob Hill': 16,
            'Russian Hill': 18
        },
        'Richmond District': {
            'Pacific Heights': 10,
            'Marina District': 9,
            'The Castro': 16,
            'Alamo Square': 13,
            'Financial District': 22,
            'Presidio': 7,
            'Mission District': 20,
            'Nob Hill': 17,
            'Russian Hill': 13
        },
        'Alamo Square': {
            'Pacific Heights': 10,
            'Marina District': 15,
            'The Castro': 8,
            'Richmond District': 11,
            'Financial District': 17,
            'Presidio': 17,
            'Mission District': 10,
            'Nob Hill': 11,
            'Russian Hill': 13
        },
        'Financial District': {
            'Pacific Heights': 13,
            'Marina District': 15,
            'The Castro': 20,
            'Richmond District': 21,
            'Alamo Square': 17,
            'Presidio': 22,
            'Mission District': 17,
            'Nob Hill': 8,
            'Russian Hill': 11
        },
        'Presidio': {
            'Pacific Heights': 11,
            'Marina District': 11,
            'The Castro': 21,
            'Richmond District': 7,
            'Alamo Square': 19,
            'Financial District': 23,
            'Mission District': 26,
            'Nob Hill': 18,
            'Russian Hill': 14
        },
        'Mission District': {
            'Pacific Heights': 16,
            'Marina District': 19,
            'The Castro': 7,
            'Richmond District': 20,
            'Alamo Square': 11,
            'Financial District': 15,
            'Presidio': 25,
            'Nob Hill': 12,
            'Russian Hill': 15
        },
        'Nob Hill': {
            'Pacific Heights': 8,
            'Marina District': 11,
            'The Castro': 17,
            'Richmond District': 14,
            'Alamo Square': 11,
            'Financial District': 9,
            'Presidio': 17,
            'Mission District': 13,
            'Russian Hill': 5
        },
        'Russian Hill': {
            'Pacific Heights': 7,
            'Marina District': 7,
            'The Castro': 21,
            'Richmond District': 14,
            'Alamo Square': 15,
            'Financial District': 11,
            'Presidio': 14,
            'Mission District': 16,
            'Nob Hill': 5
        }
    }

    # Create variables for each friend's meeting start and end times
    meet_vars = {}
    for name in friends:
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        meet_vars[name] = {'start': start_var, 'end': end_var}
        # Constrain the meeting to be within the friend's availability
        s.add(start_var >= friends[name]['start'])
        s.add(end_var <= friends[name]['end'])
        s.add(end_var == start_var + friends[name]['duration'])
        # Ensure start is before end (though duration is positive)
        s.add(start_var < end_var)

    # Current location starts at Pacific Heights at 9:00 AM (540 minutes)
    current_time = 9 * 60
    current_location = 'Pacific Heights'

    # To model the sequence of meetings, we need to define an order.
    # This is complex, so we'll assume a possible order and add constraints.
    # Alternatively, we can use a more sophisticated approach with ordering variables.
    # For simplicity, we'll proceed by adding constraints for possible sequences.

    # We'll collect all possible meetings and their times.
    # The main challenge is sequencing meetings with travel times.

    # For each pair of meetings, if one is before the other, add travel time.
    # This is a pairwise constraint.
    meeting_names = list(friends.keys())
    for i in range(len(meeting_names)):
        for j in range(i+1, len(meeting_names)):
            name1 = meeting_names[i]
            name2 = meeting_names[j]
            loc1 = friends[name1]['location']
            loc2 = friends[name2]['location']
            travel_time = travel_times[loc1][loc2]

            # Either meeting1 is before meeting2 or vice versa
            before = And(
                meet_vars[name1]['end'] + travel_time <= meet_vars[name2]['start'],
                meet_vars[name1]['start'] >= current_time
            )
            after = And(
                meet_vars[name2]['end'] + travel_times[loc2][loc1] <= meet_vars[name1]['start'],
                meet_vars[name2]['start'] >= current_time
            )
            s.add(Or(before, after))

    # Also, the first meeting must be after current_time + travel from current_location.
    # But since current_time is 9:00 AM and current_location is Pacific Heights,
    # the first meeting must start >= 9:00 AM + travel time to its location.
    for name in meeting_names:
        loc = friends[name]['location']
        travel_time = travel_times[current_location][loc]
        s.add(meet_vars[name]['start'] >= current_time + travel_time)

    # Additionally, ensure that meetings don't overlap and are properly sequenced with travel times.

    # To maximize the number of meetings, we can add a flag for each meeting indicating if it's scheduled.
    scheduled = {name: Bool(f'scheduled_{name}') for name in friends}
    for name in friends:
        s.add(Implies(scheduled[name], meet_vars[name]['start'] >= 0))  # if scheduled, start time is valid
        s.add(Implies(Not(scheduled[name]), meet_vars[name]['start'] == -1))  # if not, start is -1

    # Maximize the number of scheduled meetings
    objective = Sum([If(scheduled[name], 1, 0) for name in friends])
    s.maximize(objective)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        scheduled_meetings = []
        for name in friends:
            if m.evaluate(scheduled[name]):
                start = m.evaluate(meet_vars[name]['start']).as_long()
                end = m.evaluate(meet_vars[name]['end']).as_long()
                scheduled_meetings.append((name, start, end))
        # Sort by start time
        scheduled_meetings.sort(key=lambda x: x[1])
        for name, start, end in scheduled_meetings:
            start_hr = start // 60
            start_min = start % 60
            end_hr = end // 60
            end_min = end % 60
            print(f"Meet {name} at {friends[name]['location']} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}")
    else:
        print("No feasible schedule found.")

solve_scheduling()