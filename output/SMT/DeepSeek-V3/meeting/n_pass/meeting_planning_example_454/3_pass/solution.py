from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Friend data
    friends = [
        ("Jessica", "Golden Gate Park", 13.75, 15.0, 0.5),
        ("Ashley", "Bayview", 17.25, 20.0, 1.75),
        ("Ronald", "Chinatown", 7.25, 14.75, 1.5),
        ("William", "North Beach", 13.25, 20.25, 0.25),
        ("Daniel", "Mission District", 7.0, 11.25, 1.75)
    ]

    # Travel times in hours (from -> to -> time)
    travel = {
        "Presidio": {
            "Golden Gate Park": 12/60,
            "Bayview": 31/60,
            "Chinatown": 21/60,
            "North Beach": 18/60,
            "Mission District": 26/60,
        },
        "Golden Gate Park": {
            "Presidio": 11/60,
            "Bayview": 23/60,
            "Chinatown": 23/60,
            "North Beach": 24/60,
            "Mission District": 17/60,
        },
        "Bayview": {
            "Presidio": 31/60,
            "Golden Gate Park": 22/60,
            "Chinatown": 18/60,
            "North Beach": 21/60,
            "Mission District": 13/60,
        },
        "Chinatown": {
            "Presidio": 19/60,
            "Golden Gate Park": 23/60,
            "Bayview": 22/60,
            "North Beach": 3/60,
            "Mission District": 18/60,
        },
        "North Beach": {
            "Presidio": 17/60,
            "Golden Gate Park": 22/60,
            "Bayview": 22/60,
            "Chinatown": 6/60,
            "Mission District": 18/60,
        },
        "Mission District": {
            "Presidio": 25/60,
            "Golden Gate Park": 17/60,
            "Bayview": 15/60,
            "Chinatown": 16/60,
            "North Beach": 17/60,
        }
    }

    # Create variables
    meets = [Bool(f.name) for f in friends]
    starts = [Real(f"start_{i}") for i in range(len(friends))]
    ends = [Real(f"end_{i}") for i in range(len(friends))]
    current_loc = "Presidio"
    current_time = 9.0  # Start at 9:00 AM

    # Add constraints
    for i, (name, loc, avail_start, avail_end, min_dur) in enumerate(friends):
        # If meeting this friend
        s.add(Implies(meets[i], starts[i] >= avail_start))
        s.add(Implies(meets[i], ends[i] <= avail_end))
        s.add(Implies(meets[i], ends[i] - starts[i] >= min_dur))
        s.add(Implies(meets[i], starts[i] >= current_time + travel[current_loc][loc]))

    # No overlapping meetings
    for i in range(len(friends)):
        for j in range(i+1, len(friends)):
            s.add(Implies(And(meets[i], meets[j]),
                          Or(ends[i] <= starts[j], ends[j] <= starts[i])))

    # Maximize number of friends met
    s.maximize(Sum([If(m, 1, 0) for m in meets]))

    # Solve
    if s.check() == sat:
        m = s.model()
        result = []
        for i, (name, loc, _, _, _) in enumerate(friends):
            if is_true(m.evaluate(meets[i])):
                start = m.evaluate(starts[i])
                end = m.evaluate(ends[i])
                # Convert Z3 rational to float
                start_val = float(start.numerator_as_long())/float(start.denominator_as_long())
                end_val = float(end.numerator_as_long())/float(end.denominator_as_long())
                result.append((name, loc, start_val, end_val))
        return result
    else:
        return None

# Run solver
schedule = solve_scheduling()

# Print results
if schedule:
    print("SOLUTION:")
    for name, loc, start, end in schedule:
        print(f"Meet {name} at {loc} from {start:.2f} to {end:.2f}")
else:
    print("No feasible schedule found")