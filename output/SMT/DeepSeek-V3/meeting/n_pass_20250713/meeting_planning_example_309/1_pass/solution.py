from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Locations and their indices
    locations = {
        "Financial District": 0,
        "Chinatown": 1,
        "Alamo Square": 2,
        "Bayview": 3,
        "Fisherman's Wharf": 4
    }

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 5, 17, 19, 10],    # Financial District
        [5, 0, 17, 22, 8],     # Chinatown
        [17, 16, 0, 16, 19],   # Alamo Square
        [19, 18, 16, 0, 25],   # Bayview
        [11, 12, 20, 26, 0]     # Fisherman's Wharf
    ]

    # Friends' data: name, location, available start, available end, min duration
    friends = [
        ("Nancy", "Chinatown", 9*60 + 30, 13*60 + 30, 90),
        ("Mary", "Alamo Square", 7*60, 21*60, 75),
        ("Jessica", "Bayview", 11*60 + 15, 13*60 + 45, 45),
        ("Rebecca", "Fisherman's Wharf", 7*60, 8*60 + 30, 45)
    ]

    # Variables for each friend: start and end times
    start_vars = [Int(f"start_{name}") for name, _, _, _, _ in friends]
    end_vars = [Int(f"end_{name}") for name, _, _, _, _ in friends]
    meet_vars = [Bool(f"meet_{name}") for name, _, _, _, _ in friends]  # Whether to meet the friend

    # Initial constraints: you start at Financial District at 9:00 AM (540 minutes)
    current_time = 540
    current_location = locations["Financial District"]

    # Constraints for each friend
    for i, (name, loc, avail_start, avail_end, min_dur) in enumerate(friends):
        loc_idx = locations[loc]

        # If meeting the friend, enforce time and duration constraints
        s.add(Implies(meet_vars[i], start_vars[i] >= avail_start))
        s.add(Implies(meet_vars[i], end_vars[i] <= avail_end))
        s.add(Implies(meet_vars[i], end_vars[i] == start_vars[i] + min_dur))

        # Travel time from current location to friend's location
        travel_time = travel_times[current_location][loc_idx]

        # Ensure the start time is after current_time + travel time
        s.add(Implies(meet_vars[i], start_vars[i] >= current_time + travel_time))

        # Update current_time and current_location if meeting this friend
        new_current_time = If(meet_vars[i], end_vars[i], current_time)
        new_current_location = If(meet_vars[i], loc_idx, current_location)

        # Prepare for next friend
        current_time = new_current_time
        current_location = new_current_location

    # Objective: maximize the number of friends met
    objective = Sum([If(meet_vars[i], 1, 0) for i in range(len(friends))])
    s.maximize(objective)

    # Solve the problem
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        total_friends = 0
        for i, (name, loc, _, _, _) in enumerate(friends):
            if m.evaluate(meet_vars[i]):
                start = m.evaluate(start_vars[i]).as_long()
                end = m.evaluate(end_vars[i]).as_long()
                start_str = f"{start // 60}:{start % 60:02d}"
                end_str = f"{end // 60}:{end % 60:02d}"
                print(f"- Meet {name} at {loc} from {start_str} to {end_str}")
                total_friends += 1
        print(f"Total friends met: {total_friends}")
    else:
        print("No feasible schedule found.")

solve_scheduling()