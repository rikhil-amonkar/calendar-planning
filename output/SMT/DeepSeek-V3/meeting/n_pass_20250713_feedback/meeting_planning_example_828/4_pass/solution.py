from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the locations and their indices
    locations = {
        "Marina District": 0,
        "Richmond District": 1,
        "Union Square": 2,
        "Nob Hill": 3,
        "Fisherman's Wharf": 4,
        "Golden Gate Park": 5,
        "Embarcadero": 6,
        "Financial District": 7,
        "North Beach": 8,
        "Presidio": 9
    }

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 11, 16, 12, 10, 18, 14, 17, 11, 10],  # Marina District
        [9, 0, 21, 17, 18, 9, 19, 22, 17, 7],     # Richmond District
        [18, 20, 0, 9, 15, 22, 11, 9, 10, 24],    # Union Square
        [11, 14, 7, 0, 10, 17, 9, 9, 8, 17],      # Nob Hill
        [9, 18, 13, 11, 0, 25, 8, 11, 6, 17],     # Fisherman's Wharf
        [16, 7, 22, 20, 24, 0, 25, 26, 23, 11],   # Golden Gate Park
        [12, 21, 10, 10, 6, 25, 0, 5, 5, 20],     # Embarcadero
        [15, 21, 9, 8, 10, 23, 4, 0, 7, 22],      # Financial District
        [9, 18, 7, 7, 5, 22, 6, 8, 0, 17],        # North Beach
        [11, 7, 22, 18, 19, 12, 20, 23, 18, 0]    # Presidio
    ]

    # Friends' data: name, location, start time, end time, min duration (in minutes)
    friends = [
        ("Stephanie", "Richmond District", 16*60 + 15, 21*60 + 30, 75),
        ("William", "Union Square", 10*60 + 45, 17*60 + 30, 45),
        ("Elizabeth", "Nob Hill", 12*60 + 15, 15*60 + 0, 105),
        ("Joseph", "Fisherman's Wharf", 12*60 + 45, 14*60 + 0, 75),
        ("Anthony", "Golden Gate Park", 13*60 + 0, 20*60 + 30, 75),
        ("Barbara", "Embarcadero", 19*60 + 15, 20*60 + 30, 75),
        ("Carol", "Financial District", 11*60 + 45, 16*60 + 15, 60),
        ("Sandra", "North Beach", 10*60 + 0, 12*60 + 30, 15),
        ("Kenneth", "Presidio", 21*60 + 15, 22*60 + 15, 45)
    ]

    # Current location starts at Marina District at 9:00 AM (540 minutes)
    current_location = locations["Marina District"]
    current_time = 9 * 60

    # Variables for each friend: whether they are met, and start and end times of meeting
    meet_vars = []
    for i, (name, loc, friend_start, friend_end, min_duration) in enumerate(friends):
        met = Bool(f'met_{name}')
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        meet_vars.append((name, loc, friend_start, friend_end, min_duration, met, start, end))
        # Constraints if met
        s.add(Implies(met, start >= friend_start))
        s.add(Implies(met, end <= friend_end))
        s.add(Implies(met, end == start + min_duration))
        # If not met, set start and end to 0
        s.add(Implies(Not(met), start == 0))
        s.add(Implies(Not(met), end == 0))

    # Exactly 8 friends must be met
    s.add(Sum([If(met, 1, 0) for (_, _, _, _, _, met, _, _) in meet_vars]) == 8)

    # Add travel time constraints between consecutive meetings
    # We'll create an ordering variable to sequence the meetings
    order = [Int(f'order_{i}') for i in range(len(meet_vars))]
    s.add(Distinct(order))
    for i in range(len(order)):
        s.add(order[i] >= 0)
        s.add(order[i] < len(meet_vars))

    # For each pair of meetings, if one comes after another, add travel time constraint
    for i in range(len(meet_vars)):
        for j in range(len(meet_vars)):
            if i != j:
                name_i, loc_i, _, _, _, met_i, start_i, end_i = meet_vars[i]
                name_j, loc_j, _, _, _, met_j, start_j, _ = meet_vars[j]
                # If both are met and meeting j is after meeting i, add travel time
                s.add(Implies(And(met_i, met_j, order[i] < order[j]), 
                              start_j >= end_i + travel_times[locations[loc_i]][locations[loc_j]]))

    # Initial travel from Marina District to first meeting
    for i in range(len(meet_vars)):
        name, loc, _, _, _, met, start, _ = meet_vars[i]
        s.add(Implies(And(met, order[i] == 0), 
                      start >= current_time + travel_times[current_location][locations[loc]]))

    # Ensure no overlapping meetings
    for i in range(len(meet_vars)):
        for j in range(i + 1, len(meet_vars)):
            _, _, _, _, _, met_i, start_i, end_i = meet_vars[i]
            _, _, _, _, _, met_j, start_j, end_j = meet_vars[j]
            s.add(Implies(And(met_i, met_j), Or(end_i <= start_j, end_j <= start_i)))

    if s.check() == sat:
        m = s.model()
        schedule = []
        for name, loc, _, _, _, met, start, end in meet_vars:
            if m.evaluate(met):
                start_val = m.evaluate(start).as_long()
                end_val = m.evaluate(end).as_long()
                order_val = m.evaluate(order[meet_vars.index((name, loc, _, _, _, met, start, end))]).as_long()
                schedule.append((order_val, name, loc, start_val, end_val))
        schedule.sort()
        return [x[1:] for x in schedule]
    else:
        return None

schedule = solve_scheduling()
if schedule:
    print("SOLUTION:")
    print("Optimal Schedule (8 friends met):")
    for name, loc, start, end in schedule:
        start_hr = start // 60
        start_min = start % 60
        end_hr = end // 60
        end_min = end % 60
        print(f"Meet {name} at {loc} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}")
else:
    print("No feasible schedule found that meets exactly 8 friends.")