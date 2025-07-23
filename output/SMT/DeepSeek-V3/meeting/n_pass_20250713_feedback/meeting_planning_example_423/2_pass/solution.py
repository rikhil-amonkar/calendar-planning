from z3 import *

def solve_scheduling():
    # Initialize optimizer
    opt = Optimize()

    # Define locations and friends
    locations = ['Presidio', 'Richmond District', 'North Beach', 'Financial District', 'Golden Gate Park', 'Union Square']
    friends = {
        'Jason': {'location': 'Richmond District', 'start': 13*60, 'end': 20*60 + 45, 'duration': 90},
        'Melissa': {'location': 'North Beach', 'start': 18*60 + 45, 'end': 20*60 + 15, 'duration': 45},
        'Brian': {'location': 'Financial District', 'start': 9*60 + 45, 'end': 21*60 + 45, 'duration': 15},
        'Elizabeth': {'location': 'Golden Gate Park', 'start': 8*60 + 45, 'end': 21*60 + 30, 'duration': 105},
        'Laura': {'location': 'Union Square', 'start': 14*60 + 15, 'end': 19*60 + 30, 'duration': 75}
    }

    # Travel times matrix (in minutes)
    travel_times = {
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Financial District'): 23,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Union Square'): 22,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'North Beach'): 17,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Richmond District', 'Union Square'): 21,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Richmond District'): 18,
        ('North Beach', 'Financial District'): 8,
        ('North Beach', 'Union Square'): 7,
        ('Financial District', 'Presidio'): 22,
        ('Financial District', 'Richmond District'): 21,
        ('Financial District', 'North Beach'): 7,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Union Square'): 9,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'Richmond District'): 20,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Financial District'): 9,
        ('Union Square', 'Golden Gate Park'): 22
    }

    # Create variables for arrival and departure times at each location
    arrival = {loc: Int(f'arrival_{loc}') for loc in locations}
    departure = {loc: Int(f'departure_{loc}') for loc in locations}

    # Initial constraints: start at Presidio at 9:00 AM (540 minutes)
    opt.add(arrival['Presidio'] == 9 * 60)
    opt.add(departure['Presidio'] >= arrival['Presidio'])

    # Constraints for each friend: arrival and departure must be within their availability
    for name, info in friends.items():
        loc = info['location']
        opt.add(arrival[loc] >= info['start'])
        opt.add(departure[loc] <= info['end'])
        opt.add(departure[loc] >= arrival[loc] + info['duration'])

    # Constraints for travel times between locations
    # Ensure that if you go from A to B, departure_A + travel_time <= arrival_B
    for loc1 in locations:
        for loc2 in locations:
            if loc1 != loc2 and (loc1, loc2) in travel_times:
                opt.add(Implies(
                    And(departure[loc1] > 0, arrival[loc2] > 0),
                    departure[loc1] + travel_times[(loc1, loc2)] <= arrival[loc2]
                ))

    # Ensure all friends are met
    met_friends = []
    for name, info in friends.items():
        loc = info['location']
        met = Bool(f'met_{name}')
        opt.add(met == (departure[loc] - arrival[loc] >= info['duration']))
        met_friends.append(met)

    # Must meet exactly 5 people
    opt.add(And([m for m in met_friends]))

    # Check if a solution exists
    if opt.check() == sat:
        m = opt.model()
        print("Optimal Schedule:")
        for loc in locations:
            arr = m.evaluate(arrival[loc])
            dep = m.evaluate(departure[loc])
            if arr.as_long() > 0 or dep.as_long() > 0:
                print(f"{loc}: Arrive at {arr.as_long()//60}:{arr.as_long()%60:02d}, Depart at {dep.as_long()//60}:{dep.as_long()%60:02d}")
        print("\nMeetings:")
        for name in friends:
            loc = friends[name]['location']
            arr = m.evaluate(arrival[loc]).as_long()
            dep = m.evaluate(departure[loc]).as_long()
            dur = dep - arr
            if dur >= friends[name]['duration']:
                print(f"Met {name} at {loc} for {dur} minutes (from {arr//60}:{arr%60:02d} to {dep//60}:{dep%60:02d})")
    else:
        print("No feasible schedule found.")

solve_scheduling()