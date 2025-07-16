from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the locations and their indices
    locations = [
        "Union Square",
        "Presidio",
        "Alamo Square",
        "Marina District",
        "Financial District",
        "Nob Hill",
        "Sunset District",
        "Chinatown",
        "Russian Hill",
        "North Beach",
        "Haight-Ashbury"
    ]
    loc_index = {loc: idx for idx, loc in enumerate(locations)}

    # Travel times matrix (loc_index[from][to] = minutes)
    travel_times = [
        [0, 24, 15, 18, 9, 9, 27, 7, 13, 10, 18],  # Union Square
        [22, 0, 19, 11, 23, 18, 15, 21, 14, 18, 15],  # Presidio
        [14, 17, 0, 15, 17, 11, 16, 15, 13, 15, 5],  # Alamo Square
        [16, 10, 15, 0, 17, 12, 19, 15, 8, 11, 16],  # Marina District
        [9, 22, 17, 15, 0, 8, 30, 5, 11, 7, 19],  # Financial District
        [7, 17, 11, 11, 9, 0, 24, 6, 5, 8, 13],  # Nob Hill
        [30, 16, 17, 21, 30, 27, 0, 30, 24, 28, 15],  # Sunset District
        [7, 19, 17, 12, 5, 9, 29, 0, 7, 3, 19],  # Chinatown
        [10, 14, 15, 7, 11, 5, 23, 9, 0, 5, 17],  # Russian Hill
        [7, 17, 16, 9, 8, 7, 27, 6, 4, 0, 18],  # North Beach
        [19, 15, 5, 17, 21, 15, 15, 19, 17, 19, 0]   # Haight-Ashbury
    ]

    # Friends' data: name, location, start, end, min_duration
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

    # Create variables for each friend: start and end times
    friend_vars = []
    for friend in friends:
        name, loc, start, end, min_dur = friend
        start_var = Real(f'start_{name}')
        end_var = Real(f'end_{name}')
        s.add(start_var >= start)
        s.add(end_var <= end)
        s.add(end_var >= start_var + min_dur)
        friend_vars.append((name, loc, start_var, end_var))

    # Add constraints for travel times and no overlapping meetings
    for i in range(len(friend_vars)):
        for j in range(i + 1, len(friend_vars)):
            name1, loc1, start1, end1 = friend_vars[i]
            name2, loc2, start2, end2 = friend_vars[j]
            # Either meeting i is before j or vice versa, with travel time
            travel1 = travel_times[loc_index[loc1]][loc_index[loc2]]
            travel2 = travel_times[loc_index[loc2]][loc_index[loc1]]
            s.add(Or(
                end1 + travel1 / 60 <= start2,
                end2 + travel2 / 60 <= start1
            ))

    # Add constraint to start at Union Square at 9:00 AM
    # Assuming the first activity is to go to the first friend's location
    # We need to add travel time from Union Square to the first friend's location
    first_friend_loc = friend_vars[0][1]
    travel_to_first = travel_times[loc_index["Union Square"]][loc_index[first_friend_loc]]
    s.add(friend_vars[0][2] >= 9.0 + travel_to_first / 60)

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        schedule = []
        for name, loc, start_var, end_var in friend_vars:
            start = m[start_var].as_fraction()
            end = m[end_var].as_fraction()
            start_hr = float(start)
            end_hr = float(end)
            schedule.append((name, loc, start_hr, end_hr))
        # Sort schedule by start time
        schedule.sort(key=lambda x: x[2])
        return schedule
    else:
        return None

schedule = solve_scheduling()
if schedule:
    print("SOLUTION:")
    for name, loc, start, end in schedule:
        start_hr = int(start)
        start_min = int((start - start_hr) * 60)
        end_hr = int(end)
        end_min = int((end - end_hr) * 60)
        print(f"Meet {name} at {loc} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}")
else:
    print("No valid schedule found.")