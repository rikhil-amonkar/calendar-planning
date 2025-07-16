from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Optimize()

    # Locations and their indices
    locations = {
        'North Beach': 0,
        'Pacific Heights': 1,
        'Chinatown': 2,
        'Union Square': 3,
        'Mission District': 4,
        'Golden Gate Park': 5,
        'Nob Hill': 6
    }

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 8, 6, 7, 18, 22, 7],    # North Beach
        [9, 0, 11, 12, 15, 15, 8],  # Pacific Heights
        [3, 10, 0, 7, 18, 23, 8],   # Chinatown
        [10, 15, 7, 0, 14, 22, 9],  # Union Square
        [17, 16, 16, 15, 0, 17, 12],# Mission District
        [24, 16, 23, 22, 17, 0, 20],# Golden Gate Park
        [8, 8, 6, 7, 13, 17, 0]     # Nob Hill
    ]

    # Friends' data: name, location, start time, end time, min duration (in minutes)
    friends = [
        ('James', 1, 20*60, 22*60, 120),    # Pacific Heights, 8:00PM-10:00PM
        ('Robert', 2, 12*60 + 15, 16*60 + 45, 90),  # Chinatown, 12:15PM-4:45PM
        ('Jeffrey', 3, 9*60 + 30, 15*60 + 30, 120), # Union Square, 9:30AM-3:30PM
        ('Carol', 4, 18*60 + 15, 21*60 + 15, 15),   # Mission District, 6:15PM-9:15PM
        ('Mark', 5, 11*60 + 30, 17*60 + 45, 15),    # Golden Gate Park, 11:30AM-5:45PM
        ('Sandra', 6, 8*60, 15*60 + 30, 15)         # Nob Hill, 8:00AM-3:30PM
    ]

    # Decision variables
    meet = [Bool(f'meet_{name}') for name, _, _, _, _ in friends]
    start = [Int(f'start_{name}') for name, _, _, _, _ in friends]
    end = [Int(f'end_{name}') for name, _, _, _, _ in friends]
    order = [Int(f'order_{name}') for name, _, _, _, _ in friends]  # Sequencing variables

    # Starting point
    current_time = 9 * 60  # 9:00 AM in minutes
    current_loc = locations['North Beach']

    # Each friend's meeting must be within their availability window
    for i, (name, loc, f_start, f_end, min_dur) in enumerate(friends):
        s.add(Implies(meet[i], start[i] >= f_start))
        s.add(Implies(meet[i], end[i] <= f_end))
        s.add(Implies(meet[i], end[i] - start[i] >= min_dur))

    # All order variables must be distinct and between 0 and number of friends
    s.add(Distinct(order))
    for o in order:
        s.add(o >= 0, o < len(friends))

    # Sequencing constraints
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i != j:
                # If friend i is met before friend j
                before = And(meet[i], meet[j], order[i] < order[j])
                # Then friend j's start time must be after friend i's end time + travel time
                travel = travel_times[friends[i][1]][friends[j][1]]
                s.add(Implies(before, start[j] >= end[i] + travel))

    # Starting constraints
    for i in range(len(friends)):
        # If this is the first meeting, it must be after current time + travel time
        first_meeting = And(meet[i], order[i] == 0)
        travel = travel_times[current_loc][friends[i][1]]
        s.add(Implies(first_meeting, start[i] >= current_time + travel))

    # Maximize number of friends met
    s.maximize(Sum([If(m, 1, 0) for m in meet]))

    # Solve
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        print(f"Starting at North Beach at 9:00 AM")
        
        # Get meetings in order
        scheduled = []
        for i, (name, loc, _, _, _) in enumerate(friends):
            if m.evaluate(meet[i]):
                scheduled.append((
                    m.evaluate(order[i]).as_long(),
                    name,
                    list(locations.keys())[loc],
                    m.evaluate(start[i]).as_long(),
                    m.evaluate(end[i]).as_long()
                ))
        
        # Sort by order
        scheduled.sort()
        
        current_time = 9 * 60
        current_loc = 'North Beach'
        
        for idx, name, loc, s_time, e_time in scheduled:
            # Calculate travel time
            travel = travel_times[locations[current_loc]][locations[loc]]
            print(f"Travel from {current_loc} to {loc} ({travel} minutes)")
            
            # Convert times to readable format
            s_hr = s_time // 60
            s_min = s_time % 60
            e_hr = e_time // 60
            e_min = e_time % 60
            
            print(f"Meet {name} at {loc} from {s_hr}:{s_min:02d} to {e_hr}:{e_min:02d}")
            
            current_time = e_time
            current_loc = loc
        
        print(f"Total friends met: {len(scheduled)}")
    else:
        print("No valid schedule found")

solve_scheduling()