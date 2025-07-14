from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define districts and their indices for easy reference
    districts = [
        "Mission District",
        "Alamo Square",
        "Presidio",
        "Russian Hill",
        "North Beach",
        "Golden Gate Park",
        "Richmond District",
        "Embarcadero",
        "Financial District",
        "Marina District"
    ]
    district_index = {d: i for i, d in enumerate(districts)}

    # Travel times matrix (minutes)
    travel_times = [
        [0, 11, 25, 15, 17, 17, 20, 19, 15, 19],  # Mission District
        [10, 0, 17, 13, 15, 9, 11, 16, 17, 15],     # Alamo Square
        [26, 19, 0, 14, 18, 12, 7, 20, 23, 11],      # Presidio
        [16, 15, 14, 0, 5, 21, 14, 8, 11, 7],        # Russian Hill
        [18, 16, 17, 4, 0, 22, 18, 6, 8, 9],         # North Beach
        [17, 9, 11, 19, 23, 0, 7, 25, 26, 16],       # Golden Gate Park
        [20, 13, 7, 13, 17, 9, 0, 19, 22, 9],       # Richmond District
        [20, 19, 20, 8, 5, 25, 21, 0, 5, 12],        # Embarcadero
        [17, 17, 22, 11, 7, 23, 21, 4, 0, 15],      # Financial District
        [20, 15, 10, 8, 11, 18, 11, 14, 17, 0]       # Marina District
    ]

    # Friends' data: name, district, available start, available end, min duration (minutes)
    friends = [
        ("Laura", "Alamo Square", 14*60 + 30, 16*60 + 15, 75),
        ("Brian", "Presidio", 10*60 + 15, 17*60 + 0, 30),
        ("Karen", "Russian Hill", 18*60 + 0, 20*60 + 15, 90),
        ("Stephanie", "North Beach", 10*60 + 15, 16*60 + 0, 75),
        ("Helen", "Golden Gate Park", 11*60 + 30, 21*60 + 45, 120),
        ("Sandra", "Richmond District", 8*60 + 0, 15*60 + 15, 30),
        ("Mary", "Embarcadero", 16*60 + 45, 18*60 + 45, 120),
        ("Deborah", "Financial District", 19*60 + 0, 20*60 + 45, 105),
        ("Elizabeth", "Marina District", 8*60 + 30, 13*60 + 15, 105)
    ]

    # Current location starts at Mission District at 9:00 AM (540 minutes)
    current_time = 540
    current_district = "Mission District"

    # Variables for each friend: start time, end time, and whether they are met
    friend_vars = []
    for i, (name, district, start, end, duration) in enumerate(friends):
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        met_var = Bool(f'met_{name}')
        friend_vars.append((name, district, start, end, duration, start_var, end_var, met_var))

    # Constraints for each friend
    for (name, district, start, end, duration, start_var, end_var, met_var) in friend_vars:
        # If met, start and end must be within availability and duration must be satisfied
        s.add(Implies(met_var, And(start_var >= start, end_var <= end, end_var == start_var + duration)))
        # If not met, start and end are 0
        s.add(Implies(Not(met_var), And(start_var == 0, end_var == 0)))

    # No overlapping meetings considering travel time
    for i in range(len(friend_vars)):
        for j in range(i + 1, len(friend_vars)):
            name_i, district_i, _, _, _, start_i, end_i, met_i = friend_vars[i]
            name_j, district_j, _, _, _, start_j, end_j, met_j = friend_vars[j]
            # If both are met, then either i is before j plus travel time or vice versa
            travel_ij = travel_times[district_index[district_i]][district_index[district_j]]
            travel_ji = travel_times[district_index[district_j]][district_index[district_i]]
            s.add(Implies(And(met_i, met_j),
                          Or(end_i + travel_ij <= start_j,
                             end_j + travel_ji <= start_i)))

    # Initial travel from Mission District to first meeting
    for i, (name, district, _, _, _, start_i, _, met_i) in enumerate(friend_vars):
        travel_time = travel_times[district_index[current_district]][district_index[district]]
        s.add(Implies(met_i, start_i >= current_time + travel_time))

    # Constraint: exactly 7 friends must be met
    s.add(Sum([If(met_var, 1, 0) for (_, _, _, _, _, _, _, met_var) in friend_vars]) == 7)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        # Extract the schedule
        schedule = []
        for (name, district, _, _, _, start_var, end_var, met_var) in friend_vars:
            if m.evaluate(met_var):
                start = m.evaluate(start_var).as_long()
                end = m.evaluate(end_var).as_long()
                start_str = f"{start // 60}:{start % 60:02d}"
                end_str = f"{end // 60}:{end % 60:02d}"
                schedule.append((name, district, start_str, end_str))
        # Sort by start time
        schedule.sort(key=lambda x: x[2])
        return schedule
    else:
        return None

# Solve and print the schedule
schedule = solve_scheduling()
if schedule:
    print("SOLUTION:")
    for name, district, start, end in schedule:
        print(f"Meet {name} at {district} from {start} to {end}")
else:
    print("No feasible schedule found.")