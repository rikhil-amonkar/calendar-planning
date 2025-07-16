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

    # Create a list of all possible meeting sequences
    from itertools import permutations
    possible_orders = permutations(friends.keys())

    # We'll try different orders and pick the best one
    best_solution = None
    best_count = 0

    # Limit the number of permutations to try for efficiency
    max_permutations = 10  # Increase if needed
    for order in list(possible_orders)[:max_permutations]:
        temp_s = Solver()
        
        # Add all basic constraints
        for friend in friends:
            info = friends[friend]
            temp_s.add(Implies(meet[friend], start[friend] >= info['start']))
            temp_s.add(Implies(meet[friend], end[friend] <= info['end']))
            temp_s.add(Implies(meet[friend], end[friend] - start[friend] >= info['min_duration']))

        # Add ordering constraints for this permutation
        for i in range(1, len(order)):
            prev_friend = order[i-1]
            curr_friend = order[i]
            travel = travel_times[friends[prev_friend]['location']][friends[curr_friend]['location']]
            temp_s.add(Implies(And(meet[prev_friend], meet[curr_friend]), 
                       start[curr_friend] >= end[prev_friend] + travel))

        # Try to meet as many friends as possible in this order
        temp_s.add(Sum([If(meet[friend], 1, 0) for friend in friends]) >= best_count)

        if temp_s.check() == sat:
            m = temp_s.model()
            current_count = sum(1 for friend in friends if is_true(m.eval(meet[friend])))
            if current_count > best_count:
                best_count = current_count
                best_solution = m

    # Output the best solution found
    if best_solution:
        print("Optimal schedule found:")
        for friend in friends:
            if is_true(best_solution.eval(meet[friend])):
                print(f"Meet {friend} at {friends[friend]['location']} from {best_solution.eval(start[friend])} to {best_solution.eval(end[friend])}")
        print(f"Total friends met: {best_count}")
    else:
        print("No feasible schedule found that meets all constraints.")

solve_scheduling()