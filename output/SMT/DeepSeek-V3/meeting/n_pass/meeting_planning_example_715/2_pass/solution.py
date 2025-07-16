from z3 import *

def solve_scheduling():
    # Initialize optimizer
    opt = Optimize()

    # Friends and their details
    friends = {
        'Amanda': {'location': 'Marina District', 'start': 14*60 + 45, 'end': 19*60 + 30, 'min_duration': 105},
        'Melissa': {'location': 'The Castro', 'start': 9*60 + 30, 'end': 17*60 + 0, 'min_duration': 30},
        'Jeffrey': {'location': 'Fisherman\'s Wharf', 'start': 12*60 + 45, 'end': 18*60 + 45, 'min_duration': 120},
        'Matthew': {'location': 'Bayview', 'start': 10*60 + 15, 'end': 13*60 + 15, 'min_duration': 30},
        'Nancy': {'location': 'Pacific Heights', 'start': 17*60 + 0, 'end': 21*60 + 30, 'min_duration': 105},
        'Karen': {'location': 'Mission District', 'start': 17*60 + 30, 'end': 20*60 + 30, 'min_duration': 105},
        'Robert': {'location': 'Alamo Square', 'start': 11*60 + 15, 'end': 17*60 + 30, 'min_duration': 120},
        'Joseph': {'location': 'Golden Gate Park', 'start': 8*60 + 30, 'end': 21*60 + 15, 'min_duration': 105}
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        'Presidio': {
            'Marina District': 11,
            'The Castro': 21,
            'Fisherman\'s Wharf': 19,
            'Bayview': 31,
            'Pacific Heights': 11,
            'Mission District': 26,
            'Alamo Square': 19,
            'Golden Gate Park': 12
        },
        'Marina District': {
            'Presidio': 10,
            'The Castro': 22,
            'Fisherman\'s Wharf': 10,
            'Bayview': 27,
            'Pacific Heights': 7,
            'Mission District': 20,
            'Alamo Square': 15,
            'Golden Gate Park': 18
        },
        'The Castro': {
            'Presidio': 20,
            'Marina District': 21,
            'Fisherman\'s Wharf': 24,
            'Bayview': 19,
            'Pacific Heights': 16,
            'Mission District': 7,
            'Alamo Square': 8,
            'Golden Gate Park': 11
        },
        'Fisherman\'s Wharf': {
            'Presidio': 17,
            'Marina District': 9,
            'The Castro': 27,
            'Bayview': 26,
            'Pacific Heights': 12,
            'Mission District': 22,
            'Alamo Square': 21,
            'Golden Gate Park': 25
        },
        'Bayview': {
            'Presidio': 32,
            'Marina District': 27,
            'The Castro': 19,
            'Fisherman\'s Wharf': 25,
            'Pacific Heights': 23,
            'Mission District': 13,
            'Alamo Square': 16,
            'Golden Gate Park': 22
        },
        'Pacific Heights': {
            'Presidio': 11,
            'Marina District': 6,
            'The Castro': 16,
            'Fisherman\'s Wharf': 13,
            'Bayview': 22,
            'Mission District': 15,
            'Alamo Square': 10,
            'Golden Gate Park': 15
        },
        'Mission District': {
            'Presidio': 25,
            'Marina District': 19,
            'The Castro': 7,
            'Fisherman\'s Wharf': 22,
            'Bayview': 14,
            'Pacific Heights': 16,
            'Alamo Square': 11,
            'Golden Gate Park': 17
        },
        'Alamo Square': {
            'Presidio': 17,
            'Marina District': 15,
            'The Castro': 8,
            'Fisherman\'s Wharf': 19,
            'Bayview': 16,
            'Pacific Heights': 10,
            'Mission District': 10,
            'Golden Gate Park': 9
        },
        'Golden Gate Park': {
            'Presidio': 11,
            'Marina District': 16,
            'The Castro': 13,
            'Fisherman\'s Wharf': 24,
            'Bayview': 23,
            'Pacific Heights': 16,
            'Mission District': 17,
            'Alamo Square': 9
        }
    }

    # Decision variables: whether to meet each friend
    meet = {name: Bool(name) for name in friends}

    # Meeting start and end times (in minutes since 9:00 AM)
    start_time = {name: Int(f'start_{name}') for name in friends}
    end_time = {name: Int(f'end_{name}') for name in friends}

    # Current location starts at Presidio at 9:00 AM (time = 0)
    current_time = 0
    current_location = 'Presidio'

    # Constraints for each friend
    for name in friends:
        data = friends[name]
        loc = data['location']
        opt.add(Implies(meet[name], start_time[name] >= data['start'] - 9*60))  # Convert to minutes since 9:00 AM
        opt.add(Implies(meet[name], end_time[name] <= data['end'] - 9*60))
        opt.add(Implies(meet[name], end_time[name] - start_time[name] >= data['min_duration']))

    # No overlapping meetings and travel times
    # This is a complex part; for simplicity, we'll assume meetings are scheduled in some order
    # and travel times are respected between consecutive meetings
    # We'll use auxiliary variables to sequence meetings

    # List of friends to possibly meet
    friend_list = list(friends.keys())

    # For each pair of friends, ensure that if both are met, one is after the other plus travel time
    for i in range(len(friend_list)):
        for j in range(i+1, len(friend_list)):
            name1 = friend_list[i]
            name2 = friend_list[j]
            loc1 = friends[name1]['location']
            loc2 = friends[name2]['location']
            travel = travel_times[loc1][loc2]

            # Either name1 is before name2 or vice versa
            opt.add(Implies(And(meet[name1], meet[name2]),
                          Or(end_time[name1] + travel <= start_time[name2],
                             end_time[name2] + travel_times[loc2][loc1] <= start_time[name1])))

    # Ensure that the first meeting starts after travel from Presidio
    for name in friends:
        loc = friends[name]['location']
        travel = travel_times[current_location][loc]
        opt.add(Implies(meet[name], start_time[name] >= travel))

    # Maximize the number of friends met
    num_met = Sum([If(meet[name], 1, 0) for name in friends])
    opt.maximize(num_met)

    # Check for a solution
    if opt.check() == sat:
        m = opt.model()
        print("SOLUTION:")
        print(f"Number of friends met: {m.evaluate(num_met)}")
        scheduled = []
        for name in friends:
            if m.evaluate(meet[name]):
                start = m.evaluate(start_time[name])
                end = m.evaluate(end_time[name])
                start_hour = 9 + start // 60
                start_min = start % 60
                end_hour = 9 + end // 60
                end_min = end % 60
                scheduled.append((start, end, name, friends[name]['location']))
        scheduled.sort()
        for start, end, name, loc in scheduled:
            start_time_str = f"{start_hour}:{start_min:02d}"
            end_time_str = f"{end_hour}:{end_min:02d}"
            print(f"Meet {name} at {loc} from {start_time_str} to {end_time_str}")
    else:
        print("No solution found.")

solve_scheduling()