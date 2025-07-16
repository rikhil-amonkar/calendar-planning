from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Districts and their indices
    districts = ['Richmond', 'Sunset', 'Haight', 'Mission', 'GoldenGate']
    district_idx = {d:i for i,d in enumerate(districts)}

    # Travel times matrix (minutes)
    travel = [
        [0, 11, 10, 20, 9],
        [12, 0, 15, 24, 11],
        [10, 15, 0, 11, 7],
        [20, 24, 12, 0, 17],
        [7, 10, 7, 17, 0]
    ]

    # Friends data
    friends = [
        {'name': 'Sarah', 'district': 'Sunset', 'start': 10*60+45, 'end': 19*60, 'duration': 30},
        {'name': 'Richard', 'district': 'Haight', 'start': 11*60+45, 'end': 15*60+45, 'duration': 90},
        {'name': 'Elizabeth', 'district': 'Mission', 'start': 11*60, 'end': 17*60+15, 'duration': 120},
        {'name': 'Michelle', 'district': 'GoldenGate', 'start': 18*60+15, 'end': 20*60+45, 'duration': 90}
    ]

    # Decision variables
    arrival = {d: Int(f'arr_{d}') for d in districts}
    departure = {d: Int(f'dep_{d}') for d in districts}
    met = {f['name']: Bool(f"met_{f['name']}") for f in friends}

    # Initial constraints
    s.add(arrival['Richmond'] == 9*60)  # Start at 9:00 AM

    # Meeting constraints
    for f in friends:
        d = f['district']
        # If we meet this friend, we must be there during their window
        s.add(Implies(met[f['name']],
            And(arrival[d] <= f['start'],
                departure[d] >= f['start'] + f['duration'],
                departure[d] <= f['end'])))
        # Minimum time spent in district
        s.add(Implies(met[f['name']], departure[d] - arrival[d] >= f['duration']))

    # Travel constraints
    for d1 in districts:
        for d2 in districts:
            if d1 != d2:
                s.add(Implies(
                    And(arrival[d2] > 0, departure[d1] > 0),
                    arrival[d2] >= departure[d1] + travel[district_idx[d1]][district_idx[d2]]
                ))

    # Can't be in two places at once
    for i in range(len(districts)):
        for j in range(i+1, len(districts)):
            d1, d2 = districts[i], districts[j]
            s.add(Or(
                departure[d1] <= arrival[d2],
                departure[d2] <= arrival[d1]
            ))

    # Objective: maximize meetings
    s.maximize(Sum([If(m, 1, 0) for m in met.values()]))

    # Solve
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        for d in districts:
            arr = m[arrival[d]].as_long()
            dep = m[departure[d]].as_long()
            print(f"{d}: {arr//60:02d}:{arr%60:02d} to {dep//60:02d}:{dep%60:02d}")
        
        print("\nMeetings:")
        for f in friends:
            print(f"{f['name']}: {'✓' if m[met[f['name']]] else '✗'}")
        
        print(f"\nTotal met: {sum(1 for f in friends if m[met[f['name']]])}")
    else:
        print("No valid schedule found")

solve_scheduling()