from z3 import *

def solve_scheduling():
    # Initialize optimizer
    opt = Optimize()

    # Friends and their data
    friends = {
        'Helen': {'location': 'Golden Gate Park', 'start': 9.5, 'end': 12.25, 'min_duration': 0.75},
        'Steven': {'location': 'The Castro', 'start': 20.25, 'end': 22.0, 'min_duration': 1.75},
        'Deborah': {'location': 'Bayview', 'start': 8.5, 'end': 12.0, 'min_duration': 0.5},
        'Matthew': {'location': 'Marina District', 'start': 9.25, 'end': 14.25, 'min_duration': 0.75},
        'Joseph': {'location': 'Union Square', 'start': 14.25, 'end': 18.75, 'min_duration': 2.0},
        'Ronald': {'location': 'Sunset District', 'start': 16.0, 'end': 20.75, 'min_duration': 1.0},
        'Robert': {'location': 'Alamo Square', 'start': 18.5, 'end': 21.25, 'min_duration': 2.0},
        'Rebecca': {'location': 'Financial District', 'start': 14.75, 'end': 16.25, 'min_duration': 0.5},
        'Elizabeth': {'location': 'Mission District', 'start': 18.5, 'end': 21.0, 'min_duration': 2.0}
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        'Pacific Heights': {
            'Golden Gate Park': 15,
            'The Castro': 16,
            'Bayview': 22,
            'Marina District': 6,
            'Union Square': 12,
            'Sunset District': 21,
            'Alamo Square': 10,
            'Financial District': 13,
            'Mission District': 15
        },
        'Golden Gate Park': {
            'Pacific Heights': 16,
            'The Castro': 13,
            'Bayview': 23,
            'Marina District': 16,
            'Union Square': 22,
            'Sunset District': 10,
            'Alamo Square': 9,
            'Financial District': 26,
            'Mission District': 17
        },
        'The Castro': {
            'Pacific Heights': 16,
            'Golden Gate Park': 11,
            'Bayview': 19,
            'Marina District': 21,
            'Union Square': 19,
            'Sunset District': 17,
            'Alamo Square': 8,
            'Financial District': 21,
            'Mission District': 7
        },
        'Bayview': {
            'Pacific Heights': 23,
            'Golden Gate Park': 22,
            'The Castro': 19,
            'Marina District': 27,
            'Union Square': 18,
            'Sunset District': 23,
            'Alamo Square': 16,
            'Financial District': 19,
            'Mission District': 13
        },
        'Marina District': {
            'Pacific Heights': 7,
            'Golden Gate Park': 18,
            'The Castro': 22,
            'Bayview': 27,
            'Union Square': 16,
            'Sunset District': 19,
            'Alamo Square': 15,
            'Financial District': 17,
            'Mission District': 20
        },
        'Union Square': {
            'Pacific Heights': 15,
            'Golden Gate Park': 22,
            'The Castro': 17,
            'Bayview': 15,
            'Marina District': 18,
            'Sunset District': 27,
            'Alamo Square': 15,
            'Financial District': 9,
            'Mission District': 14
        },
        'Sunset District': {
            'Pacific Heights': 21,
            'Golden Gate Park': 11,
            'The Castro': 17,
            'Bayview': 22,
            'Marina District': 21,
            'Union Square': 30,
            'Alamo Square': 17,
            'Financial District': 30,
            'Mission District': 25
        },
        'Alamo Square': {
            'Pacific Heights': 10,
            'Golden Gate Park': 9,
            'The Castro': 8,
            'Bayview': 16,
            'Marina District': 15,
            'Union Square': 14,
            'Sunset District': 16,
            'Financial District': 17,
            'Mission District': 10
        },
        'Financial District': {
            'Pacific Heights': 13,
            'Golden Gate Park': 23,
            'The Castro': 20,
            'Bayview': 19,
            'Marina District': 15,
            'Union Square': 9,
            'Sunset District': 30,
            'Alamo Square': 17,
            'Mission District': 17
        },
        'Mission District': {
            'Pacific Heights': 16,
            'Golden Gate Park': 17,
            'The Castro': 7,
            'Bayview': 14,
            'Marina District': 19,
            'Union Square': 15,
            'Sunset District': 24,
            'Alamo Square': 11,
            'Financial District': 15
        }
    }

    # Convert travel times to hours (minutes to fractional hours)
    for from_loc in travel_times:
        for to_loc in travel_times[from_loc]:
            travel_times[from_loc][to_loc] = travel_times[from_loc][to_loc] / 60.0

    # Variables for each friend's meeting start and end times, and a flag indicating if the meeting is scheduled
    meeting_vars = {}
    for name in friends:
        start = Real(f'start_{name}')
        end = Real(f'end_{name}')
        scheduled = Bool(f'scheduled_{name}')
        meeting_vars[name] = {'start': start, 'end': end, 'scheduled': scheduled}

    # Current location starts at Pacific Heights at 9:00 AM (9.0 hours)
    current_time = 9.0
    current_location = 'Pacific Heights'

    # Constraints for each friend
    for name in friends:
        data = friends[name]
        start = meeting_vars[name]['start']
        end = meeting_vars[name]['end']
        scheduled = meeting_vars[name]['scheduled']

        # If scheduled, the meeting must fit within the friend's availability and meet the minimum duration
        opt.add(Implies(scheduled, And(
            start >= data['start'],
            end <= data['end'],
            end == start + data['min_duration']
        )))

    # Sequence constraints: order of meetings and travel times
    # Generate all possible ordered pairs of friends
    friend_names = list(friends.keys())
    for i in range(len(friend_names)):
        for j in range(len(friend_names)):
            if i == j:
                continue
            name1 = friend_names[i]
            name2 = friend_names[j]
            loc1 = friends[name1]['location']
            loc2 = friends[name2]['location']
            travel_time = travel_times[loc1][loc2]

            # If both are scheduled, then start2 >= end1 + travel_time
            opt.add(Implies(And(meeting_vars[name1]['scheduled'], meeting_vars[name2]['scheduled']),
                          meeting_vars[name2]['start'] >= meeting_vars[name1]['end'] + travel_time))

    # Additionally, the first meeting must start after current_time + travel time from current_location
    for name in friends:
        loc = friends[name]['location']
        travel_time = travel_times[current_location][loc]
        opt.add(Implies(meeting_vars[name]['scheduled'],
                      meeting_vars[name]['start'] >= current_time + travel_time))

    # Constraint to meet exactly 7 people
    total_scheduled = Sum([If(meeting_vars[name]['scheduled'], 1, 0) for name in friends])
    opt.add(total_scheduled == 7)

    # Solve the problem
    if opt.check() == sat:
        m = opt.model()
        scheduled_meetings = []
        for name in friends:
            if is_true(m.eval(meeting_vars[name]['scheduled'])):
                start_val = m.eval(meeting_vars[name]['start'])
                end_val = m.eval(meeting_vars[name]['end'])
                scheduled_meetings.append((name, float(start_val.as_fraction()), float(end_val.as_fraction())))
        
        # Sort meetings by start time
        scheduled_meetings.sort(key=lambda x: x[1])

        # Print the schedule
        print("Optimal Schedule (Meet exactly 7 friends):")
        for meeting in scheduled_meetings:
            name, start, end = meeting
            start_time = f"{int(start)}:{int((start % 1) * 60):02d}"
            end_time = f"{int(end)}:{int((end % 1) * 60):02d}"
            print(f"Meet {name} at {friends[name]['location']} from {start_time} to {end_time}")
        
        print(f"\nTotal friends met: {len(scheduled_meetings)}")
    else:
        print("No feasible schedule found that meets exactly 7 friends.")

solve_scheduling()