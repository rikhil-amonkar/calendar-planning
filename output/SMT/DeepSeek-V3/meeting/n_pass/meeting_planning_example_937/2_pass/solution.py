from z3 import *

def solve_scheduling():
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

    # Travel times from Russian Hill (minutes converted to hours)
    travel_from_russian_hill = {
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

    # Create variables for each meeting
    meeting_start = {name: Real(f"start_{name}") for name in friends}
    meeting_end = {name: Real(f"end_{name}") for name in friends}
    meets_friend = {name: Bool(f"meets_{name}") for name in friends}

    # Starting point
    current_time = Real("current_time")
    s.add(current_time == 9.0)  # Start at Russian Hill at 9:00 AM

    # Constraints for each friend
    for name in friends:
        location, start, end, duration = friends[name]
        
        # If meeting this friend, must be within their availability
        s.add(Implies(meets_friend[name], 
                     And(meeting_start[name] >= start,
                         meeting_end[name] <= end,
                         meeting_end[name] == meeting_start[name] + duration)))
        
        # Travel time from Russian Hill
        travel_time = travel_from_russian_hill[location]
        s.add(Implies(meets_friend[name], 
                     meeting_start[name] >= current_time + travel_time))

    # Can't meet friends whose windows are impossible
    for name in friends:
        _, start, end, duration = friends[name]
        if start + duration > end:
            s.add(Not(meets_friend[name]))

    # Maximize number of friends met
    s.maximize(Sum([If(meets_friend[name], 1, 0) for name in friends]))

    if s.check() == sat:
        m = s.model()
        schedule = []
        for name in friends:
            if is_true(m[meets_friend[name]]):
                start_val = m[meeting_start[name]].as_fraction()
                end_val = m[meeting_end[name]].as_fraction()
                schedule.append((
                    name,
                    float(start_val),
                    float(end_val),
                    friends[name][0]  # location
                ))
        schedule.sort(key=lambda x: x[1])  # Sort by start time
        return schedule
    else:
        return None

schedule = solve_scheduling()
if schedule:
    print("SOLUTION:")
    for name, start, end, location in schedule:
        print(f"Meet {name} at {location} from {start:.2f} to {end:.2f}")
else:
    print("No valid schedule found.")