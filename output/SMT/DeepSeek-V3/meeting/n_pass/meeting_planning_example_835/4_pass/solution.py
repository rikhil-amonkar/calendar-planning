from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Locations and their indices
    locations = {
        'Pacific Heights': 0,
        'Golden Gate Park': 1,
        'The Castro': 2,
        'Bayview': 3,
        'Marina District': 4,
        'Union Square': 5,
        'Sunset District': 6,
        'Alamo Square': 7,
        'Financial District': 8,
        'Mission District': 9
    }

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 15, 16, 22, 6, 12, 21, 10, 13, 15],
        [16, 0, 13, 23, 16, 22, 10, 9, 26, 17],
        [16, 11, 0, 19, 21, 19, 17, 8, 21, 7],
        [23, 22, 19, 0, 27, 18, 23, 16, 19, 13],
        [7, 18, 22, 27, 0, 16, 19, 15, 17, 20],
        [15, 22, 17, 15, 18, 0, 27, 15, 9, 14],
        [21, 11, 17, 22, 21, 30, 0, 17, 30, 25],
        [10, 9, 8, 16, 15, 14, 16, 0, 17, 10],
        [13, 23, 20, 19, 15, 9, 30, 17, 0, 17],
        [16, 17, 7, 14, 19, 15, 24, 11, 15, 0]
    ]

    # Friends' data
    friends = [
        ('Helen', 'Golden Gate Park', 9*60+30, 12*60+15, 45),
        ('Steven', 'The Castro', 20*60+15, 22*60+0, 105),
        ('Deborah', 'Bayview', 8*60+30, 12*60+0, 30),
        ('Matthew', 'Marina District', 9*60+15, 14*60+15, 45),
        ('Joseph', 'Union Square', 14*60+15, 18*60+45, 120),
        ('Ronald', 'Sunset District', 16*60+0, 20*60+45, 60),
        ('Robert', 'Alamo Square', 18*60+30, 21*60+15, 120),
        ('Rebecca', 'Financial District', 14*60+45, 16*60+15, 30),
        ('Elizabeth', 'Mission District', 18*60+30, 21*60+0, 120)
    ]

    # Create variables
    start_vars = [Int(f'start_{name}') for name, _, _, _, _ in friends]
    end_vars = [Int(f'end_{name}') for name, _, _, _, _ in friends]
    met_vars = [Bool(f'met_{name}') for name, _, _, _, _ in friends]

    # Initial constraints
    current_time = 540  # 9:00 AM in minutes
    current_location = locations['Pacific Heights']

    # Meeting constraints
    for i, (name, loc, start_avail, end_avail, min_dur) in enumerate(friends):
        loc_idx = locations[loc]
        travel_time = travel_times[current_location][loc_idx]
        
        # If meeting this friend
        s.add(Implies(met_vars[i], start_vars[i] >= start_avail))
        s.add(Implies(met_vars[i], end_vars[i] <= end_avail))
        s.add(Implies(met_vars[i], end_vars[i] == start_vars[i] + min_dur))
        s.add(Implies(met_vars[i], start_vars[i] >= current_time + travel_time))

    # Sequence constraints
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i != j:
                i_loc = locations[friends[i][1]]
                j_loc = locations[friends[j][1]]
                travel = travel_times[i_loc][j_loc]
                
                # Either i before j or j before i
                s.add(Implies(And(met_vars[i], met_vars[j]),
                             Or(end_vars[i] + travel <= start_vars[j],
                                end_vars[j] + travel_times[j_loc][i_loc] <= start_vars[i])))

    # Maximize number of friends met
    total_met = Sum([If(met_vars[i], 1, 0) for i in range(len(friends))])
    s.maximize(total_met)

    # Check solution
    if s.check() == sat:
        m = s.model()
        schedule = []
        for i in range(len(friends)):
            if m.evaluate(met_vars[i]):
                start = m.evaluate(start_vars[i]).as_long()
                end = m.evaluate(end_vars[i]).as_long()
                schedule.append((
                    friends[i][0],
                    friends[i][1],
                    f"{start//60}:{start%60:02d}",
                    f"{end//60}:{end%60:02d}"
                ))
        
        # Sort schedule by start time
        schedule.sort(key=lambda x: int(x[2].split(':')[0])*60 + int(x[2].split(':')[1]))
        
        print("\nOptimal Schedule:")
        print(f"Met {len(schedule)} out of {len(friends)} friends:")
        for name, loc, start, end in schedule:
            print(f"- {name} at {loc}: {start} to {end}")
    else:
        print("No feasible schedule found that meets all constraints")

solve_scheduling()