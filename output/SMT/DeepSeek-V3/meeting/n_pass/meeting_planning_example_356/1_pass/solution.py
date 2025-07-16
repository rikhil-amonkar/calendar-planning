from z3 import *

def solve_scheduling():
    s = Optimize()

    # Locations and friends' data
    friends = {
        'Barbara': {'location': 'North Beach', 'start': 13.75, 'end': 20.25, 'min_duration': 1.0},
        'Margaret': {'location': 'Presidio', 'start': 10.25, 'end': 15.25, 'min_duration': 0.5},
        'Kevin': {'location': 'Haight-Ashbury', 'start': 20.0, 'end': 20.75, 'min_duration': 0.5},
        'Kimberly': {'location': 'Union Square', 'start': 7.75, 'end': 16.75, 'min_duration': 0.5}
    }

    travel_times = {
        'Bayview': {'North Beach': 21/60, 'Presidio': 31/60, 'Haight-Ashbury': 19/60, 'Union Square': 17/60},
        'North Beach': {'Bayview': 22/60, 'Presidio': 17/60, 'Haight-Ashbury': 18/60, 'Union Square': 7/60},
        'Presidio': {'Bayview': 31/60, 'North Beach': 18/60, 'Haight-Ashbury': 15/60, 'Union Square': 22/60},
        'Haight-Ashbury': {'Bayview': 18/60, 'North Beach': 19/60, 'Presidio': 15/60, 'Union Square': 17/60},
        'Union Square': {'Bayview': 15/60, 'North Beach': 10/60, 'Presidio': 24/60, 'Haight-Ashbury': 18/60}
    }

    # Variables
    meet = {friend: Bool(f"meet_{friend}") for friend in friends}
    start = {friend: Real(f"start_{friend}") for friend in friends}
    end = {friend: Real(f"end_{friend}") for friend in friends}

    # Current time and location
    current_time = 9.0
    current_loc = 'Bayview'

    # Constraints for each friend's time window and duration
    for friend in friends:
        data = friends[friend]
        s.add(Implies(meet[friend], start[friend] >= data['start']))
        s.add(Implies(meet[friend], end[friend] <= data['end']))
        s.add(Implies(meet[friend], end[friend] - start[friend] >= data['min_duration']))

    # To model the sequence, we'll introduce variables for the order.
    # Let's assume we can meet up to 4 friends in some order.
    # We'll use a list of positions and assign each friend to a position.
    positions = 4
    pos_vars = {friend: Int(f"pos_{friend}") for friend in friends}
    s.add([And(pos_vars[friend] >= 1, pos_vars[friend] <= positions) for friend in friends])
    s.add(Distinct([pos_vars[friend] for friend in friends]))

    # Variables for the start and end times of each position
    pos_start = [Real(f"pos_start_{i}") for i in range(1, positions+1)]
    pos_end = [Real(f"pos_end_{i}") for i in range(1, positions+1)]
    pos_loc = [String(f"pos_loc_{i}") for i in range(1, positions+1)]

    # Initial position 0: start at Bayview at 9.0
    prev_start = current_time
    prev_end = current_time
    prev_loc = current_loc

    for i in range(1, positions+1):
        # The friend assigned to position i
        for friend in friends:
            s.add(Implies(pos_vars[friend] == i, meet[friend]))
            s.add(Implies(pos_vars[friend] == i, pos_start[i-1] == start[friend]))
            s.add(Implies(pos_vars[friend] == i, pos_end[i-1] == end[friend]))
            s.add(Implies(pos_vars[friend] == i, pos_loc[i-1] == friends[friend]['location']))

        # Travel time from previous location
        if i == 1:
            s.add(pos_start[i-1] >= prev_end + travel_times[prev_loc][pos_loc[i-1]])
        else:
            s.add(Implies(pos_vars[friend] == i, pos_start[i-1] >= pos_end[i-2] + travel_times[pos_loc[i-2]][pos_loc[i-1]]))

    # Ensure that if a friend is not met, their position is 0 (but positions are 1-4)
    # Alternatively, only assign positions to met friends.

    # Maximize the number of friends met
    total_met = Sum([If(meet[friend], 1, 0) for friend in friends])
    s.maximize(total_met)

    if s.check() == sat:
        model = s.model()
        print("Optimal Schedule:")
        total = 0
        scheduled = []
        for friend in friends:
            if is_true(model[meet[friend]]):
                start_val = model[start[friend]]
                end_val = model[end[friend]]
                # Convert to float for display
                start_hour = float(start_val.numerator_as_long()) / float(start_val.denominator_as_long())
                end_hour = float(end_val.numerator_as_long()) / float(end_val.denominator_as_long())
                print(f"Meet {friend} at {friends[friend]['location']} from {start_hour:.2f} to {end_hour:.2f}")
                scheduled.append((friend, start_hour, end_hour))
                total += 1
            else:
                print(f"Cannot meet {friend}")
        # Sort by start time
        scheduled.sort(key=lambda x: x[1])
        print("\nSchedule in order:")
        for entry in scheduled:
            print(f"Meet {entry[0]} from {entry[1]:.2f} to {entry[2]:.2f}")
        print(f"Total friends met: {total}")
    else:
        print("No feasible schedule found.")

solve_scheduling()