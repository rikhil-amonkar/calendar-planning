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
        'Ronald': {'loc': 1, 'start': 13*60+45, 'end': 17*60+15, 'dur': 105},
        'Patricia': {'loc': 2, 'start': 9*60+15, 'end': 22*60, 'dur': 60},
        'Laura': {'loc': 3, 'start': 12*60+30, 'end': 12*60+45, 'dur': 15},
        'Emily': {'loc': 4, 'start': 16*60+15, 'end': 18*60+30, 'dur': 60},
        'Mary': {'loc': 5, 'start': 15*60, 'end': 16*60+30, 'dur': 60}
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
        opt.add(Implies(meet[f], And(
            start[f] >= data['start'],
            end[f] <= data['end'],
            end[f] - start[f] >= data['dur'],
            start[f] >= current_time + travel[current_loc][data['loc']]
        )))
        opt.add(Implies(Not(meet[f]), And(
            start[f] == 0,
            end[f] == 0
        )))

    # Sequencing constraints
    # We'll try all possible meeting orders by allowing any permutation
    # This is more flexible than fixing an order
    for f1 in friends:
        for f2 in friends:
            if f1 != f2:
                opt.add(Implies(And(meet[f1], meet[f2]),
                    Or(
                        end[f1] + travel[friends[f1]['loc']][friends[f2]['loc']] <= start[f2],
                        end[f2] + travel[friends[f2]['loc']][friends[f1]['loc']] <= start[f1]
                    )
                ))

    # Maximize number of friends met
    opt.maximize(Sum([If(meet[f], 1, 0) for f in friends]))

    if opt.check() == sat:
        m = opt.model()
        print("Optimal schedule:")
        scheduled = []
        for f in friends:
            if m[meet[f]]:
                s = m[start[f]].as_long()
                e = m[end[f]].as_long()
                scheduled.append((s, e, f))
        
        # Sort by start time
        scheduled.sort()
        
        current = 9*60
        loc = 'Financial_District'
        for s, e, f in scheduled:
            travel_time = travel[locations[loc]][friends[f]['loc']]
            print(f"Travel from {loc} to {friends[f]['loc_name']} ({travel_time} mins)")
            print(f"Meet {f} from {s//60}:{s%60:02d} to {e//60}:{e%60:02d}")
            current = e
            loc = friends[f]['loc_name']
    else:
        print("No feasible schedule found")

# Add location names to friends data
for f in friends:
    friends[f]['loc_name'] = [k for k,v in locations.items() if v == friends[f]['loc']][0]

solve_scheduling()