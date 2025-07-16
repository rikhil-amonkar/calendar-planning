from z3 import *

def solve_scheduling():
    opt = Optimize()

    # Locations mapping
    locations = {
        'Financial_District': 0,
        'Russian_Hill': 1,
        'Sunset_District': 2,
        'North_Beach': 3,
        'The_Castro': 4,
        'Golden_Gate_Park': 5
    }

    # Travel times matrix (in minutes)
    travel = [
        [0, 10, 31, 7, 23, 23],    # Financial District
        [11, 0, 23, 5, 21, 21],     # Russian Hill
        [30, 24, 0, 29, 17, 11],    # Sunset District
        [8, 4, 27, 0, 22, 22],      # North Beach
        [20, 18, 17, 20, 0, 11],    # The Castro
        [26, 19, 10, 24, 13, 0]     # Golden Gate Park
    ]

    # Friends data
    friends = {
        'Ronald': {'loc': 1, 'loc_name': 'Russian_Hill', 'start': 13*60+45, 'end': 17*60+15, 'dur': 105},
        'Patricia': {'loc': 2, 'loc_name': 'Sunset_District', 'start': 9*60+15, 'end': 22*60, 'dur': 60},
        'Laura': {'loc': 3, 'loc_name': 'North_Beach', 'start': 12*60+30, 'end': 12*60+45, 'dur': 15},
        'Emily': {'loc': 4, 'loc_name': 'The_Castro', 'start': 16*60+15, 'end': 18*60+30, 'dur': 60},
        'Mary': {'loc': 5, 'loc_name': 'Golden_Gate_Park', 'start': 15*60, 'end': 16*60+30, 'dur': 60}
    }

    # Decision variables
    meet = {f: Bool(f'meet_{f}') for f in friends}
    start = {f: Int(f'start_{f}') for f in friends}
    end = {f: Int(f'end_{f}') for f in friends}
    current_loc = Int('current_loc')
    current_time = Int('current_time')

    # Initial conditions
    opt.add(current_loc == locations['Financial_District'])
    opt.add(current_time == 9*60)  # Start at 9:00 AM

    # Meeting constraints
    for f in friends:
        data = friends[f]
        # Create a travel time expression for each possible current location
        travel_time = Int(f'travel_{f}')
        opt.add(travel_time == If(current_loc == 0, travel[0][data['loc']],
                              If(current_loc == 1, travel[1][data['loc']],
                              If(current_loc == 2, travel[2][data['loc']],
                              If(current_loc == 3, travel[3][data['loc']],
                              If(current_loc == 4, travel[4][data['loc']],
                              travel[5][data['loc']])))))

        opt.add(Implies(meet[f], And(
            start[f] >= data['start'],
            end[f] <= data['end'],
            end[f] - start[f] >= data['dur'],
            start[f] >= current_time + travel_time
        )))
        opt.add(Implies(Not(meet[f]), And(
            start[f] == 0,
            end[f] == 0
        )))

    # Sequencing constraints
    # Create a total order of meetings
    position = {f: Int(f'pos_{f}') for f in friends}
    for f in friends:
        opt.add(position[f] >= 0)
        opt.add(position[f] < len(friends))
    
    # All positions must be distinct
    opt.add(Distinct([position[f] for f in friends]))

    # For each pair of friends, if one comes after another, enforce time constraints
    for f1 in friends:
        for f2 in friends:
            if f1 != f2:
                # Travel time from f1 to f2
                t = travel[friends[f1]['loc']][friends[f2]['loc']]
                opt.add(Implies(And(meet[f1], meet[f2], position[f1] < position[f2]),
                       end[f1] + t <= start[f2]))

    # Maximize number of friends met
    opt.maximize(Sum([If(meet[f], 1, 0) for f in friends]))

    if opt.check() == sat:
        m = opt.model()
        print("Optimal schedule found:")
        
        # Get all meetings that are scheduled
        scheduled = []
        for f in friends:
            if m[meet[f]]:
                s = m[start[f]].as_long()
                e = m[end[f]].as_long()
                p = m[position[f]].as_long()
                scheduled.append((p, s, e, f))
        
        # Sort by position
        scheduled.sort()
        
        current_time = 9*60
        current_loc = 'Financial_District'
        for p, s, e, f in scheduled:
            travel_time = travel[locations[current_loc]][friends[f]['loc']]
            print(f"{current_time//60}:{current_time%60:02d} - Travel from {current_loc} to {friends[f]['loc_name']} ({travel_time} mins)")
            print(f"{s//60}:{s%60:02d} - {e//60}:{e%60:02d} Meet {f} at {friends[f]['loc_name']}")
            current_time = e
            current_loc = friends[f]['loc_name']
        
        print("\nSummary:")
        for p, s, e, f in scheduled:
            print(f"Met {f} at {friends[f]['loc_name']} from {s//60}:{s%60:02d} to {e//60}:{e%60:02d}")
        print(f"\nTotal friends met: {len(scheduled)}")
    else:
        print("No feasible schedule found")

solve_scheduling()