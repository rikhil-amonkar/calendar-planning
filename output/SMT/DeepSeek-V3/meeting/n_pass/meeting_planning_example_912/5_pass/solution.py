from z3 import *

def solve_scheduling():
    s = Solver()

    # Locations and indices
    locations = ["Union Square", "Presidio", "Alamo Square", "Marina District", 
                "Financial District", "Nob Hill", "Sunset District", "Chinatown",
                "Russian Hill", "North Beach", "Haight-Ashbury"]
    loc_index = {loc: idx for idx, loc in enumerate(locations)}

    # Travel times matrix (minutes)
    travel = [
        [0, 24, 15, 18, 9, 9, 27, 7, 13, 10, 18],
        [22, 0, 19, 11, 23, 18, 15, 21, 14, 18, 15],
        [14, 17, 0, 15, 17, 11, 16, 15, 13, 15, 5],
        [16, 10, 15, 0, 17, 12, 19, 15, 8, 11, 16],
        [9, 22, 17, 15, 0, 8, 30, 5, 11, 7, 19],
        [7, 17, 11, 11, 9, 0, 24, 6, 5, 8, 13],
        [30, 16, 17, 21, 30, 27, 0, 30, 24, 28, 15],
        [7, 19, 17, 12, 5, 9, 29, 0, 7, 3, 19],
        [10, 14, 15, 7, 11, 5, 23, 9, 0, 5, 17],
        [7, 17, 16, 9, 8, 7, 27, 6, 4, 0, 18],
        [19, 15, 5, 17, 21, 15, 15, 19, 17, 19, 0]
    ]

    # Friends data: name, location, start (hr), end (hr), min duration (hr)
    friends = [
        ("Kimberly", "Presidio", 15.5, 16.0, 0.25),
        ("Elizabeth", "Alamo Square", 19.25, 20.25, 0.25),
        ("Joshua", "Marina District", 10.5, 14.25, 0.75),
        ("Sandra", "Financial District", 19.5, 20.25, 0.75),
        ("Kenneth", "Nob Hill", 12.75, 21.75, 0.5),
        ("Betty", "Sunset District", 14.0, 19.0, 1.0),
        ("Deborah", "Chinatown", 17.25, 20.5, 0.25),
        ("Barbara", "Russian Hill", 17.5, 21.25, 2.0),
        ("Steven", "North Beach", 17.75, 20.75, 1.5),
        ("Daniel", "Haight-Ashbury", 18.5, 18.75, 0.25)
    ]

    # Create variables and basic constraints
    vars = []
    for name, loc, start, end, dur in friends:
        s_start = Real(f'start_{name}')
        s_end = Real(f'end_{name}')
        s.add(s_start >= start)
        s.add(s_end <= end)
        s.add(s_end >= s_start + dur)
        vars.append((name, loc, s_start, s_end))

    # Add travel time constraints
    for i in range(len(vars)):
        for j in range(i+1, len(vars)):
            n1, l1, st1, et1 = vars[i]
            n2, l2, st2, et2 = vars[j]
            travel_time = RealVal(travel[loc_index[l1]][loc_index[l2]]) / 60
            s.add(Or(
                et1 + travel_time <= st2,
                et2 + travel_time <= st1
            ))

    # Starting at Union Square at 9:00 AM
    # Create a variable for first meeting and constrain it
    first_meeting = vars[0]
    travel_time = RealVal(travel[loc_index["Union Square"]][loc_index[first_meeting[1]]]) / 60
    s.add(first_meeting[2] >= 9.0 + travel_time)

    if s.check() == sat:
        m = s.model()
        schedule = []
        for name, loc, s_start, s_end in vars:
            start_val = m.evaluate(s_start)
            end_val = m.evaluate(s_end)
            start = float(start_val.numerator_as_long())/float(start_val.denominator_as_long())
            end = float(end_val.numerator_as_long())/float(end_val.denominator_as_long())
            schedule.append((name, loc, start, end))
        
        # Sort by start time for display
        schedule.sort(key=lambda x: x[2])
        
        print("SOLUTION:")
        for name, loc, start, end in schedule:
            start_hr = int(start)
            start_min = int((start - start_hr) * 60)
            end_hr = int(end)
            end_min = int((end - end_hr) * 60)
            print(f"Meet {name} at {loc} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}")
    else:
        print("No valid schedule found")

solve_scheduling()