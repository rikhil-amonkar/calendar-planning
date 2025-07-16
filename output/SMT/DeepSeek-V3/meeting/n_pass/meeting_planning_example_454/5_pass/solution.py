from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Friend data (name, location, available_start, available_end, min_duration)
    friends = [
        ("Jessica", "Golden Gate Park", 13.75, 15.0, 0.5),
        ("Ashley", "Bayview", 17.25, 20.0, 1.75),
        ("Ronald", "Chinatown", 7.25, 14.75, 1.5),
        ("William", "North Beach", 13.25, 20.25, 0.25),
        ("Daniel", "Mission District", 7.0, 11.25, 1.75)
    ]

    # Travel times in hours (from -> to -> time)
    travel = {
        "Presidio": {"Golden Gate Park": 0.2, "Bayview": 0.5167, "Chinatown": 0.35, 
                    "North Beach": 0.3, "Mission District": 0.4333},
        "Golden Gate Park": {"Presidio": 0.1833, "Bayview": 0.3833, "Chinatown": 0.3833,
                           "North Beach": 0.4, "Mission District": 0.2833},
        "Bayview": {"Presidio": 0.5167, "Golden Gate Park": 0.3667, "Chinatown": 0.3,
                   "North Beach": 0.35, "Mission District": 0.2167},
        "Chinatown": {"Presidio": 0.3167, "Golden Gate Park": 0.3833, "Bayview": 0.3667,
                     "North Beach": 0.05, "Mission District": 0.3},
        "North Beach": {"Presidio": 0.2833, "Golden Gate Park": 0.3667, "Bayview": 0.3667,
                       "Chinatown": 0.1, "Mission District": 0.3},
        "Mission District": {"Presidio": 0.4167, "Golden Gate Park": 0.2833, "Bayview": 0.25,
                            "Chinatown": 0.2667, "North Beach": 0.2833}
    }

    # Create variables
    meets = [Bool(name) for name, _, _, _, _ in friends]
    starts = [Real(f"start_{name}") for name, _, _, _, _ in friends]
    ends = [Real(f"end_{name}") for name, _, _, _, _ in friends]

    # Starting conditions
    current_loc = "Presidio"
    current_time = 9.0  # 9:00 AM

    # Add constraints for each friend
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

    # Solve and format output
    if s.check() == sat:
        m = s.model()
        result = []
        for i, (name, loc, _, _, _) in enumerate(friends):
            if is_true(m.evaluate(meets[i])):
                start = m.evaluate(starts[i])
                end = m.evaluate(ends[i])
                
                # Handle different Z3 numeric types
                def z3_to_float(val):
                    if is_rational_value(val):
                        return float(val.numerator_as_long()) / float(val.denominator_as_long())
                    elif is_algebraic_value(val):
                        return float(val.approx(10).as_decimal(10)[:-1])
                    return float(str(val))
                
                start_val = z3_to_float(start)
                end_val = z3_to_float(end)
                
                # Convert decimal hours to HH:MM format
                def format_time(h):
                    hours = int(h)
                    minutes = int(round((h - hours) * 60))
                    return f"{hours:02d}:{minutes:02d}"
                
                result.append({
                    "name": name,
                    "location": loc,
                    "start": format_time(start_val),
                    "end": format_time(end_val)
                })
        return result
    else:
        return None

# Run solver and print results
schedule = solve_scheduling()

if schedule:
    print("SOLUTION:")
    for meeting in schedule:
        print(f"Meet {meeting['name']} at {meeting['location']} from {meeting['start']} to {meeting['end']}")
else:
    print("No feasible schedule found")