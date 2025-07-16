from z3 import *

def solve_scheduling():
    # Initialize optimizer
    opt = Optimize()

    # Friends and their details
    friends = {
        'Mary': {
            'location': 'Pacific Heights',
            'available_start': 10 * 60,  # 10:00 AM in minutes
            'available_end': 19 * 60,    # 7:00 PM in minutes
            'min_duration': 45,
            'scheduled': Bool('meet_Mary')
        },
        'Lisa': {
            'location': 'Mission District',
            'available_start': 20 * 60 + 30,  # 8:30 PM in minutes
            'available_end': 22 * 60,         # 10:00 PM in minutes
            'min_duration': 75,
            'scheduled': Bool('meet_Lisa')
        },
        'Betty': {
            'location': 'Haight-Ashbury',
            'available_start': 7 * 60 + 15,  # 7:15 AM in minutes
            'available_end': 17 * 60 + 15,   # 5:15 PM in minutes
            'min_duration': 90,
            'scheduled': Bool('meet_Betty')
        },
        'Charles': {
            'location': 'Financial District',
            'available_start': 11 * 60 + 15,  # 11:15 AM in minutes
            'available_end': 15 * 60,         # 3:00 PM in minutes
            'min_duration': 120,
            'scheduled': Bool('meet_Charles')
        }
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        'Bayview': {
            'Pacific Heights': 23,
            'Mission District': 13,
            'Haight-Ashbury': 19,
            'Financial District': 19
        },
        'Pacific Heights': {
            'Bayview': 22,
            'Mission District': 15,
            'Haight-Ashbury': 11,
            'Financial District': 13
        },
        'Mission District': {
            'Bayview': 15,
            'Pacific Heights': 16,
            'Haight-Ashbury': 12,
            'Financial District': 17
        },
        'Haight-Ashbury': {
            'Bayview': 18,
            'Pacific Heights': 12,
            'Mission District': 11,
            'Financial District': 21
        },
        'Financial District': {
            'Bayview': 19,
            'Pacific Heights': 13,
            'Mission District': 17,
            'Haight-Ashbury': 19
        }
    }

    # Variables for start and end times of each meeting
    for name in friends:
        friends[name]['start'] = Int(f'start_{name}')
        friends[name]['end'] = Int(f'end_{name}')

    # Current location starts at Bayview at 9:00 AM (540 minutes)
    current_time = 9 * 60  # 9:00 AM in minutes
    current_location = 'Bayview'

    # Constraints for each friend if they are scheduled
    for name in friends:
        friend = friends[name]
        opt.add(Implies(friend['scheduled'],
              And(friend['start'] >= friend['available_start'],
                  friend['end'] <= friend['available_end'],
                  friend['end'] == friend['start'] + friend['min_duration'])))

    # Constraints for travel times and ordering
    meeting_names = list(friends.keys())
    for i in range(len(meeting_names)):
        for j in range(len(meeting_names)):
            if i != j:
                name1 = meeting_names[i]
                name2 = meeting_names[j]
                loc1 = friends[name1]['location']
                loc2 = friends[name2]['location']
                travel = travel_times[loc1][loc2]
                opt.add(Implies(And(friends[name1]['scheduled'], friends[name2]['scheduled']),
                              Or(friends[name1]['end'] + travel <= friends[name2]['start'],
                                 friends[name2]['end'] + travel <= friends[name1]['start'])))

    # The first meeting must start after current_time + travel from Bayview to the meeting's location
    for name in friends:
        loc = friends[name]['location']
        travel = travel_times[current_location][loc]
        opt.add(Implies(friends[name]['scheduled'],
                      friends[name]['start'] >= current_time + travel))

    # Objective: maximize the number of scheduled meetings
    num_meetings = Sum([If(friends[name]['scheduled'], 1, 0) for name in friends])
    opt.maximize(num_meetings)

    # Check if a solution exists
    if opt.check() == sat:
        m = opt.model()
        scheduled = []
        for name in friends:
            if m.evaluate(friends[name]['scheduled']):
                start = m.evaluate(friends[name]['start']).as_long()
                end = m.evaluate(friends[name]['end']).as_long()
                scheduled.append((name, start, end))
        # Sort by start time
        scheduled.sort(key=lambda x: x[1])
        # Print the schedule
        print("Optimal Schedule:")
        for name, start, end in scheduled:
            start_hr = start // 60
            start_min = start % 60
            end_hr = end // 60
            end_min = end % 60
            print(f"Meet {name} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d} at {friends[name]['location']}")
        print(f"Total friends met: {len(scheduled)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()