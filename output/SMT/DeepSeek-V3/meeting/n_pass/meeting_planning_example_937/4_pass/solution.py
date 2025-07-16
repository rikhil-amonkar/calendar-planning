from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Friends data: (location, start_hour, end_hour, min_duration_hours)
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
    current_time = Real("current_time")
    s.add(current_time == 9.0)

    # Add constraints for each friend
    for name in friends:
        location, f_start, f_end, duration = friends[name]
        
        # If meeting this friend, must satisfy time constraints
        s.add(Implies(meets[name],
                     And(start_times[name] >= f_start,
                         end_times[name] <= f_end,
                         end_times[name] == start_times[name] + duration,
                         start_times[name] >= current_time + travel_times[location]))

    # Maximize number of friends met
    s.maximize(Sum([If(meets[name], 1, 0) for name in friends]))

    if s.check() == sat:
        m = s.model()
        schedule = []
        for name in friends:
            if is_true(m[meets[name]]):
                # Safely convert Z3 values to floats
                start = m[start_times[name]]
                end = m[end_times[name]]
                
                if is_rational_value(start):
                    start_val = float(start.numerator_as_long()) / float(start.denominator_as_long())
                else:
                    start_val = float(str(start))
                
                if is_rational_value(end):
                    end_val = float(end.numerator_as_long()) / float(end.denominator_as_long())
                else:
                    end_val = float(str(end))
                
                schedule.append((name, friends[name][0], start_val, end_val))
        
        # Sort by start time
        schedule.sort(key=lambda x: x[2])
        
        # Format output
        print("SOLUTION:")
        for name, location, start, end in schedule:
            # Convert decimal hours to HH:MM format
            start_h = int(start)
            start_m = int(round((start - start_h) * 60))
            end_h = int(end)
            end_m = int(round((end - end_h) * 60))
            
            print(f"Meet {name} at {location} from {start_h:02d}:{start_m:02d} to {end_h:02d}:{end_m:02d}")
    else:
        print("No valid schedule found.")

# Helper function to check if a value is rational
def is_rational_value(v):
    return hasattr(v, 'numerator_as_long') and hasattr(v, 'denominator_as_long')

# Run the solver
solve_scheduling()