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
        ('Haight-Ashbury', 'Union Square'): 17/60,
        # Add reverse directions
        ('North Beach', 'Bayview'): 22/60,
        ('Presidio', 'Bayview'): 31/60,
        ('Haight-Ashbury', 'Bayview'): 18/60,
        ('Union Square', 'Bayview'): 15/60,
        ('Presidio', 'North Beach'): 18/60,
        ('Haight-Ashbury', 'North Beach'): 19/60,
        ('Union Square', 'North Beach'): 10/60,
        ('Haight-Ashbury', 'Presidio'): 15/60,
        ('Union Square', 'Presidio'): 24/60,
        ('Union Square', 'Haight-Ashbury'): 18/60
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

    # To handle ordering, we'll create position variables
    # Each friend is assigned to a position (1-4)
    position = {f: Int(f'pos_{f}') for f in friends}
    for f in friends:
        s.add(position[f] >= 1)
        s.add(position[f] <= 4)
    s.add(Distinct([position[f] for f in friends]))

    # Variables for each position's start/end time and location
    pos_start = [Real(f'pos_start_{i}') for i in range(1, 5)]
    pos_end = [Real(f'pos_end_{i}') for i in range(1, 5)]
    pos_loc = [String(f'pos_loc_{i}') for i in range(1, 5)]

    # Link friends to positions
    for f in friends:
        for i in range(1, 5):
            s.add(Implies(And(meet[f], position[f] == i),
                  And(pos_start[i-1] == start[f],
                      pos_end[i-1] == end[f],
                      pos_loc[i-1] == friends[f]['location'])))

    # Add travel time constraints between positions
    for i in range(1, 4):
        # Get travel time between position i and i+1
        travel_time = Real(f'travel_{i}')
        s.add(travel_time >= 0)
        for loc1 in ['Bayview', 'North Beach', 'Presidio', 'Haight-Ashbury', 'Union Square']:
            for loc2 in ['Bayview', 'North Beach', 'Presidio', 'Haight-Ashbury', 'Union Square']:
                if (loc1, loc2) in travel:
                    s.add(Implies(And(pos_loc[i-1] == loc1, pos_loc[i] == loc2),
                                travel_time == travel[(loc1, loc2)]))
        
        # Add time constraint
        s.add(Implies(And(position[list(friends.keys())[0]] <= i,  # If position i is used
                          position[list(friends.keys())[0]] <= i+1),  # and position i+1 is used
                      pos_start[i] >= pos_end[i-1] + travel_time))

    # Maximize number of friends met
    s.maximize(Sum([If(meet[f], 1, 0) for f in friends]))

    # Solve and print results
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        scheduled = []
        for f in friends:
            if is_true(m[meet[f]]):
                start_val = m.evaluate(start[f])
                end_val = m.evaluate(end[f])
                start_h = float(start_val.numerator_as_long())/float(start_val.denominator_as_long())
                end_h = float(end_val.numerator_as_long())/float(end_val.denominator_as_long())
                print(f"Meet {f} at {friends[f]['location']} from {start_h:.2f} to {end_h:.2f}")
                scheduled.append((f, start_h, end_h))
            else:
                print(f"Cannot meet {f}")
        
        # Print schedule in order
        scheduled.sort(key=lambda x: m.evaluate(position[x[0]]).as_long())
        print("\nSchedule in order:")
        for f, start_h, end_h in scheduled:
            print(f"Meet {f} from {start_h:.2f} to {end_h:.2f}")
        print(f"\nTotal friends met: {len(scheduled)}")
    else:
        print("No feasible schedule found")

solve_scheduling()