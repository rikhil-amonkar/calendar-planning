from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    opt = Optimize()

    # Define the districts
    districts = ['Richmond', 'Marina', 'Chinatown', 'Financial', 'Bayview', 'UnionSquare']
    district_indices = {d: i for i, d in enumerate(districts)}

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 9, 20, 22, 26, 21],    # Richmond to others
        [11, 0, 16, 17, 27, 16],   # Marina to others
        [20, 12, 0, 5, 22, 7],     # Chinatown to others
        [21, 15, 5, 0, 19, 9],     # Financial to others
        [25, 25, 18, 19, 0, 17],   # Bayview to others
        [20, 18, 7, 9, 15, 0]      # UnionSquare to others
    ]

    # Friends' data: name, district, start_available, end_available, min_duration (minutes)
    friends = [
        ('Kimberly', 'Marina', 13*60 + 15, 16*60 + 45, 15),
        ('Robert', 'Chinatown', 12*60 + 15, 20*60 + 15, 15),
        ('Rebecca', 'Financial', 13*60 + 15, 16*60 + 45, 75),
        ('Margaret', 'Bayview', 9*60 + 30, 13*60 + 30, 30),
        ('Kenneth', 'UnionSquare', 19*60 + 30, 21*60 + 15, 75)
    ]

    # Variables for each friend: start and end times of meeting
    start_vars = [Int(f'start_{name}') for name, _, _, _, _ in friends]
    end_vars = [Int(f'end_{name}') for name, _, _, _, _ in friends]

    # Current location starts at Richmond at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_district = district_indices['Richmond']

    # Track the order of meetings to ensure travel times are respected
    sequence = []

    # Constraints for each friend
    for i, (name, district, start_avail, end_avail, min_dur) in enumerate(friends):
        dist_idx = district_indices[district]

        # Meeting must start and end within friend's availability
        opt.add(start_vars[i] >= start_avail)
        opt.add(end_vars[i] <= end_avail)
        opt.add(end_vars[i] == start_vars[i] + min_dur)

        # Travel time from current district to friend's district
        travel_time = travel_times[current_district][dist_idx]
        opt.add(start_vars[i] >= current_time + travel_time)

        # Update current time and district after meeting
        current_time = end_vars[i]
        current_district = dist_idx
        sequence.append((name, start_vars[i], end_vars[i]))

    # Ensure Kenneth is met last (since his time is latest)
    kenneth_idx = [i for i, (name, _, _, _, _) in enumerate(friends) if name == 'Kenneth'][0]
    for i, (name, _, _, _, _) in enumerate(friends):
        if name != 'Kenneth':
            opt.add(end_vars[i] <= start_vars[kenneth_idx] - travel_times[district_indices[friends[i][1]]][district_indices['UnionSquare']])

    # Try to meet as many friends as possible by allowing optional meetings
    # We'll use a flag for each friend to indicate if they are met
    met_flags = [Bool(f'met_{name}') for name, _, _, _, _ in friends]
    for i in range(len(friends)):
        opt.add(Implies(met_flags[i], start_vars[i] >= 0))  # If met, start time is valid
        opt.add(Implies(Not(met_flags[i]), start_vars[i] == -1))  # If not met, start time is -1

    # Maximize the number of friends met
    opt.maximize(Sum([If(met_flags[i], 1, 0) for i in range(len(friends))]))

    # Check if a solution exists
    if opt.check() == sat:
        m = opt.model()
        print("SOLUTION:")
        total_met = 0
        for i, (name, _, _, _, _) in enumerate(friends):
            if is_true(m.evaluate(met_flags[i])):
                start = m.evaluate(start_vars[i]).as_long()
                end = m.evaluate(end_vars[i]).as_long()
                start_str = f"{start//60}:{start%60:02d}"
                end_str = f"{end//60}:{end%60:02d}"
                print(f"Meet {name} from {start_str} to {end_str} at {friends[i][1]}")
                total_met += 1
        print(f"Total friends met: {total_met}")
    else:
        print("No solution found")

solve_scheduling()