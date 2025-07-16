from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the districts
    districts = ['Richmond', 'Sunset', 'Haight', 'Mission', 'GoldenGate']
    district_indices = {d: i for i, d in enumerate(districts)}

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 11, 10, 20, 9],    # Richmond to others
        [12, 0, 15, 24, 11],    # Sunset to others
        [10, 15, 0, 11, 7],     # Haight to others
        [20, 24, 12, 0, 17],    # Mission to others
        [7, 10, 7, 17, 0]       # GoldenGate to others
    ]

    # Friends' availability and constraints
    friends = {
        'Sarah': {'district': 'Sunset', 'start': 10*60 + 45, 'end': 19*60, 'duration': 30},
        'Richard': {'district': 'Haight', 'start': 11*60 + 45, 'end': 15*60 + 45, 'duration': 90},
        'Elizabeth': {'district': 'Mission', 'start': 11*60, 'end': 17*60 + 15, 'duration': 120},
        'Michelle': {'district': 'GoldenGate', 'start': 18*60 + 15, 'end': 20*60 + 45, 'duration': 90}
    }

    # Variables for arrival and departure times at each district
    arrival = {d: Int(f'arrival_{d}') for d in districts}
    departure = {d: Int(f'departure_{d}') for d in districts}

    # Initial constraints: start at Richmond at 9:00 AM (540 minutes)
    s.add(arrival['Richmond'] == 9 * 60)
    s.add(departure['Richmond'] >= arrival['Richmond'])

    # Constraints for each friend
    for name, info in friends.items():
        district = info['district']
        start = info['start']
        end = info['end']
        duration = info['duration']
        
        # You must be in the district during the meeting time
        s.add(arrival[district] <= start)
        s.add(departure[district] >= start + duration)
        s.add(departure[district] <= end)

    # Travel constraints between districts
    for i in range(len(districts)):
        for j in range(len(districts)):
            if i != j:
                from_dist = districts[i]
                to_dist = districts[j]
                s.add(Implies(
                    And(departure[from_dist] > 0, arrival[to_dist] > 0),
                    arrival[to_dist] >= departure[from_dist] + travel_times[i][j]
                ))

    # Ensure you can't be in two places at once
    for i in range(len(districts)):
        for j in range(i+1, len(districts)):
            s.add(Or(
                departure[districts[i]] <= arrival[districts[j]],
                departure[districts[j]] <= arrival[districts[i]]
            ))

    # Objective: maximize the number of friends met
    met_friends = []
    for name in friends:
        met_friends.append(Int(f'met_{name}'))
        s.add(met_friends[-1] == If(
            And(arrival[friends[name]['district']] <= friends[name]['start'],
                departure[friends[name]['district']] >= friends[name]['start'] + friends[name]['duration'],
                departure[friends[name]['district']] <= friends[name]['end']),
            1, 0))

    total_met = sum(met_friends)
    s.maximize(total_met)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        for d in districts:
            arr = m.evaluate(arrival[d]).as_long()
            dep = m.evaluate(departure[d]).as_long()
            print(f"{d}: Arrive at {arr//60:02d}:{arr%60:02d}, Depart at {dep//60:02d}:{dep%60:02d}")
        
        print("\nMeetings:")
        for name in friends:
            met = m.evaluate(met_friends[list(friends.keys()).index(name)]).as_long()
            print(f"{name}: {'Met' if met else 'Not met'}")
        
        print(f"\nTotal friends met: {m.evaluate(total_met)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()