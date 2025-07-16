from z3 import *

def solve_scheduling():
    s = Solver()

    # Define locations and their time windows (in minutes since midnight)
    locations = {
        'Marina': (9*60, 24*60),  # Starting point
        'Embarcadero': (9*45, 18*60),
        'Bayview': (9*45, 20*15),
        'UnionSquare': (10*45, 20*15),
        'Chinatown': (7*60, 15*30),
        'Sunset': (9*60, 9*45),
        'GoldenGate': (11*60, 19*30),
        'Financial': (10*45, 11*15),
        'Haight': (19*15, 20*30),
        'Mission': (17*60, 21*45)
    }

    min_durations = {
        'Embarcadero': 105,
        'Bayview': 75,
        'UnionSquare': 120,
        'Chinatown': 60,
        'Sunset': 45,
        'GoldenGate': 45,
        'Financial': 15,
        'Haight': 15,
        'Mission': 45
    }

    # Simplified travel times (only needed routes)
    travel_times = {
        ('Marina', 'Sunset'): 19,
        ('Sunset', 'GoldenGate'): 11,
        ('GoldenGate', 'UnionSquare'): 22,
        ('UnionSquare', 'Chinatown'): 7,
        ('Chinatown', 'Financial'): 5,
        ('Financial', 'Embarcadero'): 4,
        ('Embarcadero', 'Bayview'): 21,
        ('Bayview', 'Mission'): 13,
        ('Mission', 'Haight'): 12
    }

    # Create variables
    arrival = {loc: Int(f'arr_{loc}') for loc in locations}
    departure = {loc: Int(f'dep_{loc}') for loc in locations}

    # Starting constraints
    s.add(arrival['Marina'] == 9*60)
    s.add(departure['Marina'] == 9*60)

    # Location constraints
    for loc in locations:
        if loc == 'Marina':
            continue
        start, end = locations[loc]
        s.add(arrival[loc] >= start)
        s.add(departure[loc] <= end)
        s.add(departure[loc] >= arrival[loc] + min_durations.get(loc, 0))

    # Define visit order
    order = ['Marina', 'Sunset', 'GoldenGate', 'UnionSquare', 
             'Chinatown', 'Financial', 'Embarcadero', 'Bayview', 
             'Mission', 'Haight']

    # Travel time constraints
    for i in range(len(order)-1):
        from_loc = order[i]
        to_loc = order[i+1]
        s.add(arrival[to_loc] >= departure[from_loc] + travel_times[(from_loc, to_loc)])

    # Solve and print
    if s.check() == sat:
        m = s.model()
        print("Feasible schedule:")
        for loc in order:
            if loc == 'Marina':
                continue
            arr = m.evaluate(arrival[loc]).as_long()
            dep = m.evaluate(departure[loc]).as_long()
            print(f"{loc}: {arr//60:02d}:{arr%60:02d} - {dep//60:02d}:{dep%60:02d}")
    else:
        print("No feasible schedule found")

solve_scheduling()