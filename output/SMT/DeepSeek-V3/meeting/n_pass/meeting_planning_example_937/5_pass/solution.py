from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Friends data: name -> (location, start_time, end_time, min_duration)
    friends = {
        "David": ("Sunset District", 9.25, 22.0, 0.25),
        "Kenneth": ("Union Square", 21.25, 21.75, 0.25),
        "Patricia": ("Nob Hill", 15.0, 19.25, 2.0),
        "Mary": ("Marina District", 14.75, 16.75, 0.75),
        "Charles": ("Richmond District", 17.25, 21.0, 0.25),
        "Joshua": ("Financial District", 14.5, 17.25, 1.5),
        "Ronald": ("Embarcadero", 18.25, 20.75, 0.5),
        "George": ("The Castro", 14.25, 19.0, 1.75),
        "Kimberly": ("Alamo Square", 9.0, 14.5, 1.75),
        "William": ("Presidio", 7.0, 12.75, 1.0)
    }

    # Travel times from Russian Hill (in hours)
    travel_times = {
        "Sunset District": 23/60,
        "Union Square": 10/60,
        "Nob Hill": 5/60,
        "Marina District": 7/60,
        "Richmond District": 14/60,
        "Financial District": 11/60,
        "Embarcadero": 8/60,
        "The Castro": 21/60,
        "Alamo Square": 15/60,
        "Presidio": 14/60
    }

    # Create variables
    meets = {name: Bool(f"meets_{name}") for name in friends}
    start_times = {name: Real(f"start_{name}") for name in friends}
    end_times = {name: Real(f"end_{name}") for name in friends}

    # Starting at Russian Hill at 9:00 AM
    s.add(And([start_times[name] >= 0 for name in friends]))

    # Add constraints for each friend
    for name in friends:
        location, f_start, f_end, duration = friends[name]
        
        # If meeting this friend, must satisfy time constraints
        s.add(Implies(meets[name],
                     And(start_times[name] >= f_start,
                         end_times[name] <= f_end,
                         end_times[name] == start_times[name] + duration,
                         start_times[name] >= 9.0 + travel_times[location]))

    # No overlapping meetings (simplified - assumes meetings are sequential)
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                s.add(Implies(And(meets[name1], meets[name2]),
                              Or(end_times[name1] <= start_times[name2],
                                 end_times[name2] <= start_times[name1])))

    # Maximize number of friends met
    s.maximize(Sum([If(meets[name], 1, 0) for name in friends]))

    if s.check() == sat:
        m = s.model()
        schedule = []
        for name in friends:
            if is_true(m[meets[name]]):
                # Get start and end times
                start = m[start_times[name]]
                end = m[end_times[name]]
                
                # Convert to float safely
                def z3_to_float(v):
                    if is_rational_value(v):
                        return float(v.numerator_as_long())/float(v.denominator_as_long())
                    return float(str(v))
                
                start_val = z3_to_float(start)
                end_val = z3_to_float(end)
                
                schedule.append((name, friends[name][0], start_val, end_val))
        
        # Sort by start time
        schedule.sort(key=lambda x: x[2])
        
        # Format output
        print("SOLUTION:")
        for name, location, start, end in schedule:
            # Convert decimal hours to HH:MM format
            def decimal_to_time(decimal):
                hours = int(decimal)
                minutes = int(round((decimal - hours) * 60))
                return f"{hours:02d}:{minutes:02d}"
            
            print(f"Meet {name} at {location} from {decimal_to_time(start)} to {decimal_to_time(end)}")
    else:
        print("No valid schedule found.")

def is_rational_value(v):
    return hasattr(v, 'numerator_as_long') and hasattr(v, 'denominator_as_long')

# Run the solver
solve_scheduling()