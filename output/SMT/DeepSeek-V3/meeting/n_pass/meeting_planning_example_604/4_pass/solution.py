from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Locations and their indices
    locations = {
        "Fisherman's Wharf": 0,
        "The Castro": 1,
        "Golden Gate Park": 2,
        "Embarcadero": 3,
        "Russian Hill": 4,
        "Nob Hill": 5,
        "Alamo Square": 6,
        "North Beach": 7
    }

    # Travel times matrix (from_location_index, to_location_index) -> minutes
    travel_times = [
        [0, 26, 25, 8, 7, 11, 20, 6],    # Fisherman's Wharf
        [24, 0, 11, 22, 18, 16, 8, 20],   # The Castro
        [24, 13, 0, 25, 19, 20, 10, 24],  # Golden Gate Park
        [6, 25, 25, 0, 8, 10, 19, 5],     # Embarcadero
        [7, 21, 21, 8, 0, 5, 15, 5],      # Russian Hill
        [11, 17, 17, 9, 5, 0, 11, 8],     # Nob Hill
        [19, 8, 9, 17, 13, 11, 0, 15],    # Alamo Square
        [5, 22, 22, 6, 4, 7, 16, 0]       # North Beach
    ]

    # Friends data: name, location, start_available, end_available, min_duration (minutes)
    friends = [
        ("Laura", "The Castro", 19*60 + 45, 21*60 + 30, 105),  # 7:45PM to 9:30PM
        ("Daniel", "Golden Gate Park", 21*60 + 15, 21*60 + 45, 15),  # 9:15PM to 9:45PM
        ("William", "Embarcadero", 7*60, 9*60, 90),  # 7:00AM to 9:00AM
        ("Karen", "Russian Hill", 14*60 + 30, 19*60 + 45, 30),  # 2:30PM to 7:45PM
        ("Stephanie", "Nob Hill", 7*60 + 30, 9*60 + 30, 45),  # 7:30AM to 9:30AM
        ("Joseph", "Alamo Square", 11*60 + 30, 12*60 + 45, 15),  # 11:30AM to 12:45PM
        ("Kimberly", "North Beach", 15*60 + 45, 19*60 + 15, 30)  # 3:45PM to 7:15PM
    ]

    # Create variables for each friend: start time, end time, and whether they are met
    friend_vars = []
    for name, loc, start_avail, end_avail, min_dur in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        met = Bool(f'met_{name}')
        friend_vars.append((name, loc, start, end, met, start_avail, end_avail, min_dur))
        # Constraints for meeting time within availability
        s.add(Implies(met, start >= start_avail))
        s.add(Implies(met, end <= end_avail))
        s.add(Implies(met, end == start + min_dur))
        s.add(Implies(Not(met), start == 0))
        s.add(Implies(Not(met), end == 0))

    # Constraint: You start at Fisherman's Wharf at 9:00AM (540 minutes)
    current_time = 9 * 60  # 9:00AM in minutes
    current_location = locations["Fisherman's Wharf"]

    # To manage the order of meetings, we need to sequence them. However, with Z3, it's complex to model dynamic ordering.
    # Alternative approach: for each possible pair of meetings, if both are met, then the second must start after the first's end plus travel time.
    for i in range(len(friend_vars)):
        name_i, loc_i, start_i, end_i, met_i, _, _, _ = friend_vars[i]
        loc_i_index = locations[loc_i]
        for j in range(len(friend_vars)):
            if i == j:
                continue
            name_j, loc_j, start_j, end_j, met_j, _, _, _ = friend_vars[j]
            loc_j_index = locations[loc_j]
            travel_ij = travel_times[loc_i_index][loc_j_index]
            # If both are met, then start_j >= end_i + travel_ij
            s.add(Implies(And(met_i, met_j), start_j >= end_i + travel_ij))

    # Ensure the first meeting starts after current_time + travel from Fisherman's Wharf
    for i in range(len(friend_vars)):
        name_i, loc_i, start_i, end_i, met_i, _, _, _ = friend_vars[i]
        loc_i_index = locations[loc_i]
        travel_time = travel_times[current_location][loc_i_index]
        s.add(Implies(met_i, start_i >= current_time + travel_time))

    # Maximize the number of friends met
    met_friends = [met for (_, _, _, _, met, _, _, _) in friend_vars]
    total_met = Sum([If(met, 1, 0) for met in met_friends])
    s.maximize(total_met)

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        scheduled_meetings = []
        for name, loc, start, end, met, _, _, _ in friend_vars:
            if m.evaluate(met):
                start_val = m.evaluate(start).as_long()
                end_val = m.evaluate(end).as_long()
                start_h = start_val // 60
                start_m = start_val % 60
                end_h = end_val // 60
                end_m = end_val % 60
                scheduled_meetings.append((start_val, name, loc, start_h, start_m, end_h, end_m))
        scheduled_meetings.sort()
        for _, name, loc, start_h, start_m, end_h, end_m in scheduled_meetings:
            print(f"Meet {name} at {loc} from {start_h:02d}:{start_m:02d} to {end_h:02d}:{end_m:02d}")
        print(f"Total friends met: {m.evaluate(total_met)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()