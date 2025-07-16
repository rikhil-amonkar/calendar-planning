from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Friends' availability and locations
    friends = {
        'Nancy': {'location': 'Chinatown', 'start': 9.5, 'end': 13.5, 'min_duration': 1.5},
        'Mary': {'location': 'Alamo Square', 'start': 7.0, 'end': 21.0, 'min_duration': 1.25},
        'Jessica': {'location': 'Bayview', 'start': 11.25, 'end': 13.75, 'min_duration': 0.75},
        'Rebecca': {'location': 'Fisherman\'s Wharf', 'start': 7.0, 'end': 8.5, 'min_duration': 0.75}
    }

    # Travel times (in hours) between locations
    travel_times = {
        'Financial District': {'Chinatown': 5/60, 'Alamo Square': 17/60, 'Bayview': 19/60, 'Fisherman\'s Wharf': 10/60},
        'Chinatown': {'Financial District': 5/60, 'Alamo Square': 17/60, 'Bayview': 22/60, 'Fisherman\'s Wharf': 8/60},
        'Alamo Square': {'Financial District': 17/60, 'Chinatown': 16/60, 'Bayview': 16/60, 'Fisherman\'s Wharf': 19/60},
        'Bayview': {'Financial District': 19/60, 'Chinatown': 18/60, 'Alamo Square': 16/60, 'Fisherman\'s Wharf': 25/60},
        'Fisherman\'s Wharf': {'Financial District': 11/60, 'Chinatown': 12/60, 'Alamo Square': 20/60, 'Bayview': 26/60}
    }

    # Decision variables
    meet = {friend: Bool(f'meet_{friend}') for friend in friends}
    start = {friend: Real(f'start_{friend}') for friend in friends}
    end = {friend: Real(f'end_{friend}') for friend in friends}

    # Constraints for each friend
    for friend in friends:
        info = friends[friend]
        s.add(Implies(meet[friend], start[friend] >= info['start']))
        s.add(Implies(meet[friend], end[friend] <= info['end']))
        s.add(Implies(meet[friend], end[friend] - start[friend] >= info['min_duration']))

    # Initial conditions
    current_time = 9.0  # Start at Financial District at 9:00 AM
    current_location = 'Financial District'

    # Ordering constraints (simplified)
    # We'll assume a fixed order for simplicity: Rebecca -> Nancy -> Jessica -> Mary
    # This can be generalized with more complex constraints if needed
    order = ['Rebecca', 'Nancy', 'Jessica', 'Mary']
    for i in range(len(order)):
        friend = order[i]
        if i > 0:
            prev_friend = order[i-1]
            # Travel time from previous location to current friend's location
            travel = travel_times[friends[prev_friend]['location']][friends[friend]['location']]
            s.add(Implies(And(meet[prev_friend], meet[friend]), start[friend] >= end[prev_friend] + travel))

    # Objective: maximize the number of friends met
    s.maximize(Sum([If(meet[friend], 1, 0) for friend in friends]))

    # Solve
    if s.check() == sat:
        m = s.model()
        print("Optimal schedule:")
        total = 0
        for friend in friends:
            if is_true(m.eval(meet[friend])):
                total += 1
                print(f"Meet {friend} at {friends[friend]['location']} from {m.eval(start[friend])} to {m.eval(end[friend])}")
        print(f"Total friends met: {total}")
    else:
        print("No feasible schedule found.")

solve_scheduling()