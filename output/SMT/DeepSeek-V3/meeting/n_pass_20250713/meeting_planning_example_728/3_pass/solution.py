from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes - 540  # 9:00 AM is 540 minutes

    # Friends' availability and constraints
    friends = {
        'Karen': {'location': 'Mission District', 'start': time_to_minutes('14:15'), 'end': time_to_minutes('22:00'), 'duration': 30},
        'Richard': {'location': 'Fisherman\'s Wharf', 'start': time_to_minutes('14:30'), 'end': time_to_minutes('17:30'), 'duration': 30},
        'Robert': {'location': 'Presidio', 'start': time_to_minutes('21:45'), 'end': time_to_minutes('22:45'), 'duration': 60},
        'Joseph': {'location': 'Union Square', 'start': time_to_minutes('11:45'), 'end': time_to_minutes('14:45'), 'duration': 120},
        'Helen': {'location': 'Sunset District', 'start': time_to_minutes('14:45'), 'end': time_to_minutes('20:45'), 'duration': 105},
        'Elizabeth': {'location': 'Financial District', 'start': time_to_minutes('10:00'), 'end': time_to_minutes('12:45'), 'duration': 75},
        'Kimberly': {'location': 'Haight-Ashbury', 'start': time_to_minutes('14:15'), 'end': time_to_minutes('17:30'), 'duration': 105},
        'Ashley': {'location': 'Russian Hill', 'start': time_to_minutes('11:30'), 'end': time_to_minutes('21:30'), 'duration': 45}
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        'Marina District': {
            'Mission District': 20,
            'Fisherman\'s Wharf': 10,
            'Presidio': 10,
            'Union Square': 16,
            'Sunset District': 19,
            'Financial District': 17,
            'Haight-Ashbury': 16,
            'Russian Hill': 8
        },
        'Mission District': {
            'Marina District': 19,
            'Fisherman\'s Wharf': 22,
            'Presidio': 25,
            'Union Square': 15,
            'Sunset District': 24,
            'Financial District': 15,
            'Haight-Ashbury': 12,
            'Russian Hill': 15
        },
        'Fisherman\'s Wharf': {
            'Marina District': 9,
            'Mission District': 22,
            'Presidio': 17,
            'Union Square': 13,
            'Sunset District': 27,
            'Financial District': 11,
            'Haight-Ashbury': 22,
            'Russian Hill': 7
        },
        'Presidio': {
            'Marina District': 11,
            'Mission District': 26,
            'Fisherman\'s Wharf': 19,
            'Union Square': 22,
            'Sunset District': 15,
            'Financial District': 23,
            'Haight-Ashbury': 15,
            'Russian Hill': 14
        },
        'Union Square': {
            'Marina District': 18,
            'Mission District': 14,
            'Fisherman\'s Wharf': 15,
            'Presidio': 24,
            'Sunset District': 27,
            'Financial District': 9,
            'Haight-Ashbury': 18,
            'Russian Hill': 13
        },
        'Sunset District': {
            'Marina District': 21,
            'Mission District': 25,
            'Fisherman\'s Wharf': 29,
            'Presidio': 16,
            'Union Square': 30,
            'Financial District': 30,
            'Haight-Ashbury': 15,
            'Russian Hill': 24
        },
        'Financial District': {
            'Marina District': 15,
            'Mission District': 17,
            'Fisherman\'s Wharf': 10,
            'Presidio': 22,
            'Union Square': 9,
            'Sunset District': 30,
            'Haight-Ashbury': 19,
            'Russian Hill': 11
        },
        'Haight-Ashbury': {
            'Marina District': 17,
            'Mission District': 11,
            'Fisherman\'s Wharf': 23,
            'Presidio': 15,
            'Union Square': 19,
            'Sunset District': 15,
            'Financial District': 21,
            'Russian Hill': 17
        },
        'Russian Hill': {
            'Marina District': 7,
            'Mission District': 16,
            'Fisherman\'s Wharf': 7,
            'Presidio': 14,
            'Union Square': 10,
            'Sunset District': 23,
            'Financial District': 11,
            'Haight-Ashbury': 17
        }
    }

    # Create variables for each friend's meeting start and end times
    meeting_starts = {}
    meeting_ends = {}
    is_scheduled = {}
    for name in friends:
        meeting_starts[name] = Int(f'start_{name}')
        meeting_ends[name] = Int(f'end_{name}')
        is_scheduled[name] = Int(f'scheduled_{name}')
        s.add(Or(is_scheduled[name] == 0, is_scheduled[name] == 1))

    # Current location starts at Marina District
    current_location = 'Marina District'

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        s.add(Implies(is_scheduled[name] == 1, meeting_starts[name] >= friend['start']))
        s.add(Implies(is_scheduled[name] == 1, meeting_ends[name] <= friend['end']))
        s.add(Implies(is_scheduled[name] == 1, meeting_ends[name] - meeting_starts[name] >= friend['duration']))

    # Ensure all friends are met
    s.add(Sum([is_scheduled[name] for name in friends]) == 8)

    # Ensure no overlapping meetings and travel time between consecutive meetings
    # We'll use a list to represent the order of meetings
    order = [name for name in friends]
    for i in range(len(order) - 1):
        name1 = order[i]
        name2 = order[i + 1]
        location1 = friends[name1]['location']
        location2 = friends[name2]['location']
        travel_time = travel_times[location1][location2]
        s.add(Implies(And(is_scheduled[name1] == 1, is_scheduled[name2] == 1),
                      meeting_starts[name2] >= meeting_ends[name1] + travel_time))

    # Check if the solution is feasible
    if s.check() == sat:
        m = s.model()
        print("Feasible schedule found:")
        for name in sorted(friends.keys()):
            if m[is_scheduled[name]].as_long() == 1:
                start = m[meeting_starts[name]].as_long()
                end = m[meeting_ends[name]].as_long()
                start_time = f"{9 + start // 60}:{start % 60:02d}"
                end_time = f"{9 + end // 60}:{end % 60:02d}"
                print(f"{name}: {start_time} to {end_time} at {friends[name]['location']}")
    else:
        print("No feasible schedule found.")

solve_scheduling()