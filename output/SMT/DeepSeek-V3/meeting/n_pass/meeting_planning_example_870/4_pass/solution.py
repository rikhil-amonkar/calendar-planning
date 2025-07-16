from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

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

    # Corrected travel times dictionary
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

    # Create a list to track the order of meetings
    meeting_order = []
    for name in friends:
        meeting_order.append((name, friends[name]['location']))

    # Add constraints for travel times between consecutive meetings
    for i in range(len(meeting_order)-1):
        name1, loc1 = meeting_order[i]
        name2, loc2 = meeting_order[i+1]
        travel_time = travel_times[loc1][loc2]
        s.add(meet_vars[name2]['start'] >= meet_vars[name1]['end'] + travel_time)

    # Ensure first meeting starts after current time + travel time
    first_name, first_loc = meeting_order[0]
    first_travel = travel_times[current_location][first_loc]
    s.add(meet_vars[first_name]['start'] >= current_time + first_travel)

    # To maximize the number of meetings, we can add a flag for each meeting
    scheduled = {name: Bool(f'scheduled_{name}') for name in friends}
    for name in friends:
        s.add(Implies(scheduled[name], meet_vars[name]['start'] >= 0))
        s.add(Implies(Not(scheduled[name]), meet_vars[name]['start'] == -1))

    # Maximize the number of scheduled meetings
    objective = Sum([If(scheduled[name], 1, 0) for name in friends])
    s.maximize(objective)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        scheduled_meetings = []
        for name in friends:
            if is_true(m.evaluate(scheduled[name])):
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