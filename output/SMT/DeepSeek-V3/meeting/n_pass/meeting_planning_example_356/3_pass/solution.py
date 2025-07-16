from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Friends' data
    friends = {
        'Barbara': {'location': 'North Beach', 'start': 13.75, 'end': 20.25, 'min_duration': 1.0},
        'Margaret': {'location': 'Presidio', 'start': 10.25, 'end': 15.25, 'min_duration': 0.5},
        'Kevin': {'location': 'Haight-Ashbury', 'start': 20.0, 'end': 20.75, 'min_duration': 0.5},
        'Kimberly': {'location': 'Union Square', 'start': 7.75, 'end': 16.75, 'min_duration': 0.5}
    }

    # Travel times dictionary: from -> to -> minutes
    travel_times = {
        'Bayview': {'North Beach': 21/60, 'Presidio': 31/60, 'Haight-Ashbury': 19/60, 'Union Square': 17/60},
        'North Beach': {'Bayview': 22/60, 'Presidio': 17/60, 'Haight-Ashbury': 18/60, 'Union Square': 7/60},
        'Presidio': {'Bayview': 31/60, 'North Beach': 18/60, 'Haight-Ashbury': 15/60, 'Union Square': 22/60},
        'Haight-Ashbury': {'Bayview': 18/60, 'North Beach': 19/60, 'Presidio': 15/60, 'Union Square': 17/60},
        'Union Square': {'Bayview': 15/60, 'North Beach': 10/60, 'Presidio': 24/60, 'Haight-Ashbury': 18/60}
    }

    # Variables for each friend's meeting start and end times, and whether they are met
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

    # Define possible orders (heuristic)
    # We'll try to meet Kimberly first (since she's available earliest), then Margaret, then Barbara, then Kevin.
    # Alternatively, other orders may be possible.

    # For each friend, if they are met, their start time must be after the previous friend's end time plus travel time.
    # We'll model this by assuming a specific order and adding constraints accordingly.

    # Assume order: Kimberly -> Margaret -> Barbara -> Kevin
    order = ['Kimberly', 'Margaret', 'Barbara', 'Kevin']

    # Variables to represent the start and end times of each position
    pos_start = [Real(f"pos_start_{i}") for i in range(len(order))]
    pos_end = [Real(f"pos_end_{i}") for i in range(len(order))]
    pos_loc = [friends[friend]['location'] for friend in order]

    # Initial position: start at Bayview at 9.0
    prev_end = current_time
    prev_loc = current_loc

    for i in range(len(order)):
        friend = order[i]
        s.add(Implies(meet[friend], pos_start[i] == start[friend]))
        s.add(Implies(meet[friend], pos_end[i] == end[friend]))
        s.add(Implies(meet[friend], pos_start[i] >= prev_end + travel_times[prev_loc][pos_loc[i]]))
        prev_end = pos_end[i]
        prev_loc = pos_loc[i]

    # Maximize the number of friends met
    total_met = Sum([If(meet[friend], 1, 0) for friend in friends])
    s.maximize(total_met)

    # Check if the solver can find a solution
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