from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Optimize()

    # Locations mapping
    locations = {
        'North Beach': 0,
        'Pacific Heights': 1,
        'Chinatown': 2,
        'Union Square': 3,
        'Mission District': 4,
        'Golden Gate Park': 5,
        'Nob Hill': 6
    }

    # Travel times matrix (minutes)
    travel = [
        [0, 8, 6, 7, 18, 22, 7],    # North Beach
        [9, 0, 11, 12, 15, 15, 8],   # Pacific Heights
        [3, 10, 0, 7, 18, 23, 8],    # Chinatown
        [10, 15, 7, 0, 14, 22, 9],   # Union Square
        [17, 16, 16, 15, 0, 17, 12], # Mission District
        [24, 16, 23, 22, 17, 0, 20], # Golden Gate Park
        [8, 8, 6, 7, 13, 17, 0]      # Nob Hill
    ]

    # Friends data: name, location, start, end, min_duration (minutes)
    friends = [
        ('James', 1, 20*60, 22*60, 120),      # 8PM-10PM
        ('Robert', 2, 12*60+15, 16*60+45, 90), # 12:15PM-4:45PM
        ('Jeffrey', 3, 9*60+30, 15*60+30, 120),# 9:30AM-3:30PM
        ('Carol', 4, 18*60+15, 21*60+15, 15),  # 6:15PM-9:15PM
        ('Mark', 5, 11*60+30, 17*60+45, 15),   # 11:30AM-5:45PM
        ('Sandra', 6, 8*60, 15*60+30, 15)     # 8AM-3:30PM
    ]

    # Decision variables
    meet = [Bool(f'meet_{name}') for name, _, _, _, _ in friends]
    start_times = [Int(f'start_{name}') for name, _, _, _, _ in friends]
    end_times = [Int(f'end_{name}') for name, _, _, _, _ in friends]
    visit_order = [Int(f'order_{name}') for name, _, _, _, _ in friends]

    # Starting point
    current_time = 9 * 60  # 9:00 AM
    current_loc = locations['North Beach']

    # Basic meeting constraints
    for i, (name, loc, f_start, f_end, min_dur) in enumerate(friends):
        s.add(Implies(meet[i], start_times[i] >= f_start))
        s.add(Implies(meet[i], end_times[i] <= f_end))
        s.add(Implies(meet[i], end_times[i] - start_times[i] >= min_dur))
        s.add(Implies(Not(meet[i]), start_times[i] == -1))
        s.add(Implies(Not(meet[i]), end_times[i] == -1))

    # Visit order constraints
    s.add(Distinct(visit_order))
    for o in visit_order:
        s.add(o >= 0, o < len(friends))

    # Sequencing constraints
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i != j:
                # If meeting i comes before meeting j
                cond = And(meet[i], meet[j], visit_order[i] < visit_order[j])
                # Then j must start after i ends plus travel time
                travel_time = travel[friends[i][1]][friends[j][1]]
                s.add(Implies(cond, start_times[j] >= end_times[i] + travel_time))

    # First meeting must be after travel from starting location
    for i in range(len(friends)):
        first = And(meet[i], visit_order[i] == 0)
        travel_time = travel[current_loc][friends[i][1]]
        s.add(Implies(first, start_times[i] >= current_time + travel_time))

    # Maximize number of friends met
    s.maximize(Sum([If(m, 1, 0) for m in meet]))

    # Solve and print results
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        print(f"Starting at North Beach at 9:00 AM")
        
        # Collect scheduled meetings
        scheduled = []
        for i, (name, loc, _, _, _) in enumerate(friends):
            if m.evaluate(meet[i]):
                scheduled.append((
                    m.evaluate(visit_order[i]).as_long(),
                    name,
                    list(locations.keys())[loc],
                    m.evaluate(start_times[i]).as_long(),
                    m.evaluate(end_times[i]).as_long()
                ))
        
        # Sort by visit order
        scheduled.sort()
        
        current_loc_name = 'North Beach'
        current_time = 9 * 60
        
        for order, name, loc, start, end in scheduled:
            # Calculate travel time
            travel_time = travel[locations[current_loc_name]][locations[loc]]
            print(f"Travel from {current_loc_name} to {loc} ({travel_time} minutes)")
            
            # Format times
            start_hr = start // 60
            start_min = start % 60
            end_hr = end // 60
            end_min = end % 60
            
            print(f"Meet {name} at {loc} from {start_hr}:{start_min:02d} to {end_hr}:{end_min:02d}")
            
            current_time = end
            current_loc_name = loc
        
        print(f"\nTotal friends met: {len(scheduled)}")
    else:
        print("No valid schedule found")

solve_scheduling()