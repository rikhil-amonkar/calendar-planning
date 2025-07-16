from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Friends and their details
    friends = {
        'Kenneth': {'location': 'Richmond District', 'start_avail': 21*60 + 15, 'end_avail': 22*60, 'min_duration': 30},
        'Lisa': {'location': 'Union Square', 'start_avail': 9*60, 'end_avail': 16*60 + 30, 'min_duration': 45},
        'Joshua': {'location': 'Financial District', 'start_avail': 12*60, 'end_avail': 15*60 + 15, 'min_duration': 15},
        'Nancy': {'location': 'Pacific Heights', 'start_avail': 8*60, 'end_avail': 11*60 + 30, 'min_duration': 90},
        'Andrew': {'location': 'Nob Hill', 'start_avail': 11*60 + 30, 'end_avail': 20*60 + 15, 'min_duration': 60},
        'John': {'location': 'Bayview', 'start_avail': 16*60 + 45, 'end_avail': 21*60 + 30, 'min_duration': 75}
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        'Embarcadero': {
            'Richmond District': 21,
            'Union Square': 10,
            'Financial District': 5,
            'Pacific Heights': 11,
            'Nob Hill': 10,
            'Bayview': 21
        },
        'Richmond District': {
            'Embarcadero': 19,
            'Union Square': 21,
            'Financial District': 22,
            'Pacific Heights': 10,
            'Nob Hill': 17,
            'Bayview': 26
        },
        'Union Square': {
            'Embarcadero': 11,
            'Richmond District': 20,
            'Financial District': 9,
            'Pacific Heights': 15,
            'Nob Hill': 9,
            'Bayview': 15
        },
        'Financial District': {
            'Embarcadero': 4,
            'Richmond District': 21,
            'Union Square': 9,
            'Pacific Heights': 13,
            'Nob Hill': 8,
            'Bayview': 19
        },
        'Pacific Heights': {
            'Embarcadero': 10,
            'Richmond District': 12,
            'Union Square': 12,
            'Financial District': 13,
            'Nob Hill': 8,
            'Bayview': 22
        },
        'Nob Hill': {
            'Embarcadero': 9,
            'Richmond District': 14,
            'Union Square': 7,
            'Financial District': 9,
            'Pacific Heights': 8,
            'Bayview': 19
        },
        'Bayview': {
            'Embarcadero': 19,
            'Richmond District': 25,
            'Union Square': 17,
            'Financial District': 19,
            'Pacific Heights': 23,
            'Nob Hill': 20
        }
    }

    # Create variables for each friend's meeting start and end times (in minutes since midnight)
    meeting_start = {name: Int(f'start_{name}') for name in friends}
    meeting_end = {name: Int(f'end_{name}') for name in friends}

    # Current location starts at Embarcadero at 9:00 AM (540 minutes)
    current_time = 9 * 60
    current_location = 'Embarcadero'

    # Constraints for each friend's meeting time within their availability
    for name in friends:
        info = friends[name]
        s.add(meeting_start[name] >= info['start_avail'])
        s.add(meeting_end[name] <= info['end_avail'])
        s.add(meeting_end[name] == meeting_start[name] + info['min_duration'])

    # Ensure that the first meeting starts after traveling from Embarcadero
    for name in friends:
        loc = friends[name]['location']
        travel_time = travel_times[current_location][loc]
        s.add(meeting_start[name] >= current_time + travel_time)

    # Ensure no overlapping meetings considering travel time
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                loc1 = friends[name1]['location']
                loc2 = friends[name2]['location']
                travel_time = travel_times[loc1][loc2]
                s.add(Or(
                    meeting_end[name1] + travel_time <= meeting_start[name2],
                    meeting_end[name2] + travel_time <= meeting_start[name1]
                ))

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        # Extract the meeting times
        schedule = []
        for name in friends:
            start = m.evaluate(meeting_start[name]).as_long()
            end = m.evaluate(meeting_end[name]).as_long()
            schedule.append((name, start, end))
        # Sort by start time
        schedule.sort(key=lambda x: x[1])
        # Print the schedule
        print("Feasible schedule found:")
        for name, start, end in schedule:
            start_hr = start // 60
            start_min = start % 60
            end_hr = end // 60
            end_min = end % 60
            print(f"Meet {name} at {friends[name]['location']} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}")
    else:
        print("No feasible schedule found.")

solve_scheduling()