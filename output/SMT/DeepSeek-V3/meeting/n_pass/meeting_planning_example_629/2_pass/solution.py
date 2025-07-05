from z3 import *

def solve_scheduling():
    # Initialize optimizer
    opt = Optimize()

    # Locations and their indices
    locations = {
        'Russian Hill': 0,
        'Presidio': 1,
        'Chinatown': 2,
        'Pacific Heights': 3,
        'Richmond District': 4,
        'Fisherman\'s Wharf': 5,
        'Golden Gate Park': 6,
        'Bayview': 7
    }

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 14, 9, 7, 14, 7, 21, 23],  # Russian Hill
        [14, 0, 21, 11, 7, 19, 12, 31],  # Presidio
        [7, 19, 0, 10, 20, 8, 23, 22],   # Chinatown
        [7, 11, 11, 0, 12, 13, 15, 22],  # Pacific Heights
        [13, 7, 20, 10, 0, 18, 9, 26],   # Richmond District
        [7, 17, 12, 12, 18, 0, 25, 26],  # Fisherman's Wharf
        [19, 11, 23, 16, 7, 24, 0, 23],  # Golden Gate Park
        [23, 31, 18, 23, 25, 25, 22, 0]  # Bayview
    ]

    # Friends' data: name, location, start_availability, end_availability, min_duration (minutes)
    friends = [
        ('Matthew', 'Presidio', 11*60, 21*60, 90),
        ('Margaret', 'Chinatown', 9*60+15, 18*60+45, 90),
        ('Nancy', 'Pacific Heights', 14*60+15, 17*60, 15),
        ('Helen', 'Richmond District', 19*60+45, 22*60, 60),
        ('Rebecca', 'Fisherman\'s Wharf', 21*60+15, 22*60+15, 60),
        ('Kimberly', 'Golden Gate Park', 13*60, 16*60+30, 120),
        ('Kenneth', 'Bayview', 14*60+30, 18*60, 60)
    ]

    # Variables for each friend: start and end times of meeting
    start_vars = [Int(f'start_{name}') for name, _, _, _, _ in friends]
    end_vars = [Int(f'end_{name}') for name, _, _, _, _ in friends]
    meet_vars = [Bool(f'meet_{name}') for name, _, _, _, _ in friends]

    # Initial position and time
    current_location = locations['Russian Hill']
    current_time = 9 * 60  # 9:00 AM in minutes

    # Constraints for each friend
    for i, (name, loc, avail_start, avail_end, min_dur) in enumerate(friends):
        loc_idx = locations[loc]
        # Must meet each friend exactly once
        opt.add(meet_vars[i] == True)
        # Meeting must fit within their availability
        opt.add(start_vars[i] >= avail_start)
        opt.add(end_vars[i] <= avail_end)
        opt.add(end_vars[i] == start_vars[i] + min_dur)

    # Sequence constraints: travel time between meetings
    # We need to order the meetings and account for travel time
    # For simplicity, we'll assume a fixed order and let Z3 handle the timing
    # Here, we'll enforce that the start time of the next meeting is after the end time of the previous meeting plus travel time
    for i in range(len(friends) - 1):
        loc_i = locations[friends[i][1]]
        loc_j = locations[friends[i+1][1]]
        travel_time = travel_times[loc_i][loc_j]
        opt.add(start_vars[i+1] >= end_vars[i] + travel_time)

    # Ensure the first meeting starts after travel time from Russian Hill
    first_loc = locations[friends[0][1]]
    travel_time = travel_times[current_location][first_loc]
    opt.add(start_vars[0] >= current_time + travel_time)

    # Check if a solution exists
    if opt.check() == sat:
        m = opt.model()
        print("SOLUTION:")
        print(f"Start at Russian Hill at 9:00 AM")
        current_time = 9 * 60
        current_location = locations['Russian Hill']
        met_friends = []

        for i, (name, loc, _, _, _) in enumerate(friends):
            start = m.evaluate(start_vars[i]).as_long()
            end = m.evaluate(end_vars[i]).as_long()
            loc_idx = locations[loc]
            travel_time = travel_times[current_location][loc_idx]
            departure_time = start - travel_time
            if departure_time < current_time:
                departure_time = current_time
                start = departure_time + travel_time
                end = start + friends[i][4]
            print(f"Travel from {list(locations.keys())[current_location]} to {loc} at {departure_time//60}:{departure_time%60:02d} (travel time: {travel_time} mins)")
            print(f"Meet {name} at {loc} from {start//60}:{start%60:02d} to {end//60}:{end%60:02d}")
            current_time = end
            current_location = loc_idx
            met_friends.append(name)

        print(f"\nMet all {len(met_friends)} friends: {', '.join(met_friends)}")
    else:
        print("No solution found")

solve_scheduling()