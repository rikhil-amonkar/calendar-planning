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

    # Travel times in hours (convert from minutes)
    travel = {
        ('Bayview', 'North Beach'): 21/60,
        ('Bayview', 'Presidio'): 31/60,
        ('Bayview', 'Haight-Ashbury'): 19/60,
        ('Bayview', 'Union Square'): 17/60,
        ('North Beach', 'Presidio'): 17/60,
        ('North Beach', 'Haight-Ashbury'): 18/60,
        ('North Beach', 'Union Square'): 7/60,
        ('Presidio', 'Haight-Ashbury'): 15/60,
        ('Presidio', 'Union Square'): 22/60,
        ('Haight-Ashbury', 'Union Square'): 17/60
    }

    # Create variables
    meet = {f: Bool(f'meet_{f}') for f in friends}
    start = {f: Real(f'start_{f}') for f in friends}
    end = {f: Real(f'end_{f}') for f in friends}

    # Current location and time
    current_loc = 'Bayview'
    current_time = 9.0

    # Basic constraints for each friend
    for f in friends:
        data = friends[f]
        s.add(Implies(meet[f], start[f] >= data['start']))
        s.add(Implies(meet[f], end[f] <= data['end']))
        s.add(Implies(meet[f], end[f] - start[f] >= data['min_duration']))

    # Constraints for meeting order and travel times
    # We'll consider all possible meeting sequences
    # For simplicity, we'll assume a maximum of 4 meetings (one per friend)
    # and add constraints for possible sequences

    # Possible sequences (all permutations of friends)
    from itertools import permutations
    possible_sequences = list(permutations(friends.keys())
    
    # For each possible sequence, add constraints if that sequence is chosen
    for seq in possible_sequences:
        # Create variables for this sequence
        seq_meet = [meet[f] for f in seq]
        seq_start = [start[f] for f in seq]
        seq_end = [end[f] for f in seq]
        seq_loc = [friends[f]['location'] for f in seq]
        
        # Add constraints for this sequence
        prev_end = current_time
        prev_loc = current_loc
        for i in range(len(seq)):
            f = seq[i]
            # If meeting this friend in this sequence
            s.add(Implies(And(*seq_meet[:i+1]), 
                        And(seq_start[i] >= prev_end + travel.get((prev_loc, seq_loc[i]), 0),
                            seq_end[i] == seq_start[i] + friends[f]['min_duration'])))
            prev_end = seq_end[i]
            prev_loc = seq_loc[i]

    # Maximize number of friends met
    s.maximize(Sum([If(meet[f], 1, 0) for f in friends]))

    # Solve and print results
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        scheduled = []
        for f in friends:
            if is_true(m[meet[f]]):
                start_val = m[start[f]].as_fraction()
                end_val = m[end[f]].as_fraction()
                start_h = float(start_val.numerator)/float(start_val.denominator)
                end_h = float(end_val.numerator)/float(end_val.denominator)
                print(f"Meet {f} at {friends[f]['location']} from {start_h:.2f} to {end_h:.2f}")
                scheduled.append((f, start_h, end_h))
            else:
                print(f"Cannot meet {f}")
        
        # Print schedule in order
        scheduled.sort(key=lambda x: x[1])
        print("\nSchedule in order:")
        for f, start_h, end_h in scheduled:
            print(f"Meet {f} from {start_h:.2f} to {end_h:.2f}")
        print(f"\nTotal friends met: {len(scheduled)}")
    else:
        print("No feasible schedule found")

solve_scheduling()