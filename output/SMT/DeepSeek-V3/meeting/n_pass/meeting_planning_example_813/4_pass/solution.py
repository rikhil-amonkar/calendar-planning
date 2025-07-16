from z3 import *

def solve_scheduling():
    s = Solver()

    # Define locations with consistent naming (no spaces)
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

    # Travel times between consecutive locations in our planned route
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
        s.add(departure[loc] >= arrival[loc] + min_durations.get(loc, 0))

    # Define our planned visit order
    visit_order = [
        'Marina', 'Sunset', 'GoldenGate', 'UnionSquare',
        'Chinatown', 'Financial', 'Embarcadero', 'Bayview',
        'Mission', 'Haight'
    ]

    # Add travel time constraints between consecutive locations
    for i in range(len(visit_order)-1):
        from_loc = visit_order[i]
        to_loc = visit_order[i+1]
        s.add(arrival[to_loc] >= departure[from_loc] + travel_times[(from_loc, to_loc)])

    # Check for a feasible solution
    if s.check() == sat:
        m = s.model()
        print("Feasible schedule found:\n")
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
        print("No feasible schedule found that meets all constraints")

solve_scheduling()