from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define districts and their indices
    districts = [
        "Marina District",
        "Bayview",
        "Sunset District",
        "Richmond District",
        "Nob Hill",
        "Chinatown",
        "Haight-Ashbury",
        "North Beach",
        "Russian Hill",
        "Embarcadero"
    ]
    district_index = {d: i for i, d in enumerate(districts)}

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 27, 19, 11, 12, 15, 16, 11, 8, 14],    # Marina District
        [27, 0, 23, 25, 20, 19, 19, 22, 23, 19],   # Bayview
        [21, 22, 0, 12, 27, 30, 15, 28, 24, 30],   # Sunset District
        [9, 27, 11, 0, 17, 20, 10, 17, 13, 19],    # Richmond District
        [11, 19, 24, 14, 0, 6, 13, 8, 5, 9],       # Nob Hill
        [12, 20, 29, 20, 9, 0, 19, 3, 7, 5],       # Chinatown
        [17, 18, 15, 10, 15, 19, 0, 19, 17, 20],   # Haight-Ashbury
        [9, 25, 27, 18, 7, 6, 18, 0, 4, 6],        # North Beach
        [7, 23, 23, 14, 5, 9, 17, 5, 0, 8],        # Russian Hill
        [12, 21, 30, 21, 10, 7, 21, 5, 8, 0]       # Embarcadero
    ]

    # Friends' data: name, district, start time, end time, min duration (minutes)
    friends = [
        ("Charles", "Bayview", 11*60 + 30, 14*60 + 30, 45),
        ("Robert", "Sunset District", 16*60 + 45, 21*60, 30),
        ("Karen", "Richmond District", 19*60 + 15, 21*60 + 30, 60),
        ("Rebecca", "Nob Hill", 16*60 + 15, 20*60 + 30, 90),
        ("Margaret", "Chinatown", 14*60 + 15, 19*60 + 45, 120),
        ("Patricia", "Haight-Ashbury", 14*60 + 30, 20*60 + 30, 45),
        ("Mark", "North Beach", 14*60, 18*60 + 30, 105),
        ("Melissa", "Russian Hill", 13*60, 19*60 + 45, 30),
        ("Laura", "Embarcadero", 7*60 + 45, 13*60 + 15, 105)
    ]

    # Start at Marina District at 9:00 AM (540 minutes)
    current_time = 540
    current_location = district_index["Marina District"]

    # Variables for each meeting: start, end, and whether the meeting is scheduled
    meeting_vars = []
    for i, (name, district, start, end, duration) in enumerate(friends):
        start_var = Int(f"start_{name}")
        end_var = Int(f"end_{name}")
        scheduled = Bool(f"scheduled_{name}")
        meeting_vars.append((name, district, start_var, end_var, scheduled, duration))
        s.add(start_var >= start, end_var <= end)
        s.add(end_var == start_var + duration)
        s.add(Or(Not(scheduled), And(start_var >= start, end_var <= end)))

    # Ensure meetings don't overlap and account for travel time
    for i in range(len(meeting_vars)):
        for j in range(i + 1, len(meeting_vars)):
            name_i, district_i, start_i, end_i, scheduled_i, dur_i = meeting_vars[i]
            name_j, district_j, start_j, end_j, scheduled_j, dur_j = meeting_vars[j]
            # If both are scheduled, they must not overlap considering travel time
            travel_ij = travel_times[district_index[district_i]][district_index[district_j]]
            travel_ji = travel_times[district_index[district_j]][district_index[district_i]]
            s.add(Implies(And(scheduled_i, scheduled_j),
                          Or(end_i + travel_ij <= start_j,
                             end_j + travel_ji <= start_i)))

    # First meeting must be after arrival and travel time
    for i, (name, district, start, end, scheduled, dur) in enumerate(meeting_vars):
        travel_time = travel_times[current_location][district_index[district]]
        s.add(Implies(scheduled, start >= current_time + travel_time))

    # Constraint: exactly 8 friends must be met
    total_met = Sum([If(scheduled, 1, 0) for (_, _, _, _, scheduled, _) in meeting_vars])
    s.add(total_met == 8)

    # Solve the problem
    if s.check() == sat:
        m = s.model()
        scheduled_meetings = []
        for name, district, start_var, end_var, scheduled, dur in meeting_vars:
            if is_true(m[scheduled]):
                start = m[start_var].as_long()
                end = m[end_var].as_long()
                scheduled_meetings.append((name, district, start, end, dur))
        
        # Sort meetings by start time
        scheduled_meetings.sort(key=lambda x: x[2])

        # Print the schedule
        print("SOLUTION:")
        print("Optimal Schedule:")
        current_location = "Marina District"
        current_time = 540
        for name, district, start, end, dur in scheduled_meetings:
            travel_time = travel_times[district_index[current_location]][district_index[district]]
            print(f"Travel from {current_location} to {district}: {travel_time} minutes")
            print(f"Meet {name} at {district} from {start//60:02d}:{start%60:02d} to {end//60:02d}:{end%60:02d} ({dur} minutes)")
            current_location = district
            current_time = end
        print(f"Total friends met: {len(scheduled_meetings)}")
    else:
        print("No solution found")

solve_scheduling()