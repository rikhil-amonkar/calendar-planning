from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define locations and their time windows (in minutes since midnight)
    locations = {
        'Marina': (9*60, 24*60),       # Starting location
        'Embarcadero': (9*45, 18*60),   # Joshua
        'Bayview': (9*45, 20*15),       # Jeffrey
        'UnionSquare': (10*45, 20*15),  # Charles
        'Chinatown': (7*60, 15*30),     # Joseph
        'Sunset': (9*60, 9*45),         # Elizabeth
        'GoldenGate': (11*60, 19*30),   # Matthew
        'Financial': (10*45, 11*15),    # Carol
        'Haight': (19*15, 20*30),       # Paul
        'Mission': (17*60, 21*45)       # Rebecca
    }

    # Minimum meeting durations (minutes)
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

    # Travel times between locations (minutes)
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

    # Create variables for arrival and departure times
    arrival = {loc: Int(f'arr_{loc}') for loc in locations}
    departure = {loc: Int(f'dep_{loc}') for loc in locations}

    # Starting constraints at Marina District
    s.add(arrival['Marina'] == 9*60)
    s.add(departure['Marina'] == 9*60)

    # Add constraints for each location
    for loc in locations:
        if loc == 'Marina':
            continue
        start, end = locations[loc]
        s.add(arrival[loc] >= start)
        s.add(departure[loc] <= end)
        s.add(departure[loc] >= arrival[loc] + min_durations[loc])

    # Define visit order
    visit_order = [
        'Marina', 'Sunset', 'GoldenGate', 'UnionSquare',
        'Chinatown', 'Financial', 'Embarcadero', 'Bayview',
        'Mission', 'Haight'
    ]

    # Add travel time constraints
    for i in range(len(visit_order)-1):
        from_loc = visit_order[i]
        to_loc = visit_order[i+1]
        s.add(arrival[to_loc] >= departure[from_loc] + travel_times[(from_loc, to_loc)])

    # Check for solution
    if s.check() == sat:
        m = s.model()
        print("OPTIMAL SCHEDULE FOUND:\n")
        print("{:<15} {:<12} {:<12}".format("Location", "Arrival", "Departure"))
        print("-"*40)
        
        for loc in visit_order:
            if loc == 'Marina':
                continue
            arr = m.evaluate(arrival[loc]).as_long()
            dep = m.evaluate(departure[loc]).as_long()
            print("{:<15} {:02d}:{:02d}     {:02d}:{:02d}".format(
                loc, arr//60, arr%60, dep//60, dep%60))
    else:
        print("No feasible schedule exists that meets all constraints")

# Run the solver
solve_scheduling()