from z3 import *

def solve_scheduling():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Define districts and their indices
    districts = ['Richmond', 'Marina', 'Chinatown', 'Financial', 'Bayview', 'UnionSquare']
    district_indices = {d: i for i, d in enumerate(districts)}

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 9, 20, 22, 26, 21],    # Richmond to others
        [11, 0, 16, 17, 27, 16],    # Marina to others
        [20, 12, 0, 5, 22, 7],      # Chinatown to others
        [21, 15, 5, 0, 19, 9],      # Financial to others
        [25, 25, 18, 19, 0, 17],    # Bayview to others
        [20, 18, 7, 9, 15, 0]       # UnionSquare to others
    ]

    # Friends' data: name, district, start_available, end_available, min_duration (minutes)
    friends = [
        ('Margaret', 'Bayview', 9*60 + 30, 13*60 + 30, 30),
        ('Robert', 'Chinatown', 12*60 + 15, 20*60 + 15, 15),
        ('Kimberly', 'Marina', 13*60 + 15, 16*60 + 45, 15),
        ('Rebecca', 'Financial', 13*60 + 15, 16*60 + 45, 75),
        ('Kenneth', 'UnionSquare', 19*60 + 30, 21*60 + 15, 75)
    ]

    # Variables for each friend: start and end times of meeting
    start_vars = [Int(f'start_{name}') for name, _, _, _, _ in friends]
    end_vars = [Int(f'end_{name}') for name, _, _, _, _ in friends]

    # Variables to track current location and time
    current_time = Int('initial_time')
    current_district = Int('initial_district')
    opt.add(current_time == 540)  # Start at 9:00 AM (540 minutes)
    opt.add(current_district == district_indices['Richmond'])

    # Constraints for each friend
    for i, (name, district, start_avail, end_avail, min_dur) in enumerate(friends):
        dist_idx = district_indices[district]

        # Meeting must start and end within friend's availability
        opt.add(start_vars[i] >= start_avail)
        opt.add(end_vars[i] <= end_avail)
        opt.add(end_vars[i] == start_vars[i] + min_dur)

        # Travel time from current location to friend's district
        travel_time = travel_times[current_district][dist_idx]
        opt.add(start_vars[i] >= current_time + travel_time)

        # Update current time and district after meeting
        current_time = end_vars[i]
        current_district = dist_idx

    # Ensure Kenneth is met last (since his time is latest)
    kenneth_idx = [i for i, (name, _, _, _, _) in enumerate(friends) if name == 'Kenneth'][0]
    for i, (name, _, _, _, _) in enumerate(friends):
        if name != 'Kenneth':
            opt.add(end_vars[i] <= start_vars[kenneth_idx] - travel_times[district_indices[friends[i][1]]][district_indices['UnionSquare']])

    # Try to meet all friends (since it's possible in this case)
    for i in range(len(friends)):
        opt.add(start_vars[i] >= 0)

    # Check if a solution exists
    if opt.check() == sat:
        m = opt.model()
        print("SOLUTION:")
        schedule = []
        for i, (name, district, _, _, _) in enumerate(friends):
            start = m.evaluate(start_vars[i]).as_long()
            end = m.evaluate(end_vars[i]).as_long()
            start_str = f"{start//60}:{start%60:02d}"
            end_str = f"{end//60}:{end%60:02d}"
            schedule.append((start, name, district, start_str, end_str))
        
        # Sort by start time
        schedule.sort()
        for _, name, district, start_str, end_str in schedule:
            print(f"Meet {name} from {start_str} to {end_str} at {district}")
        print(f"Total friends met: {len(friends)}")
    else:
        print("No solution found")

solve_scheduling()