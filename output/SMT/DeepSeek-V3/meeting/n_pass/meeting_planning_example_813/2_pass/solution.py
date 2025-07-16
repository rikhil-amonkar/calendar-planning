from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the locations and their available time windows (in minutes since midnight)
    locations = {
        'Marina District': (9*60, 24*60),  # Starting point, no meeting
        'Embarcadero': (9*45, 18*60),      # Joshua
        'Bayview': (9*45, 20*15),          # Jeffrey
        'Union Square': (10*45, 20*15),    # Charles
        'Chinatown': (7*60, 15*30),        # Joseph
        'Sunset District': (9*60, 9*45),   # Elizabeth
        'Golden Gate Park': (11*60, 19*30), # Matthew
        'Financial District': (10*45, 11*15), # Carol
        'Haight-Ashbury': (19*15, 20*30),  # Paul
        'Mission District': (17*60, 21*45)  # Rebecca
    }

    # Minimum meeting durations in minutes
    min_durations = {
        'Embarcadero': 105,
        'Bayview': 75,
        'Union Square': 120,
        'Chinatown': 60,
        'Sunset District': 45,
        'Golden Gate Park': 45,
        'Financial District': 15,
        'Haight-Ashbury': 15,
        'Mission District': 45
    }

    # Travel times between locations (in minutes)
    travel_times = {
        ('Marina District', 'Embarcadero'): 14,
        ('Marina District', 'Bayview'): 27,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'Chinatown'): 15,
        ('Marina District', 'Sunset District'): 19,
        ('Marina District', 'Golden Gate Park'): 18,
        ('Marina District', 'Financial District'): 17,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'Mission District'): 20,
        ('Embarcadero', 'Marina District'): 12,
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Union Square'): 10,
        ('Embarcadero', 'Chinatown'): 7,
        ('Embarcadero', 'Sunset District'): 30,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Financial District'): 5,
        ('Embarcadero', 'Haight-Ashbury'): 21,
        ('Embarcadero', 'Mission District'): 20,
        ('Bayview', 'Marina District'): 27,
        ('Bayview', 'Embarcadero'): 19,
        ('Bayview', 'Union Square'): 18,
        ('Bayview', 'Chinatown'): 19,
        ('Bayview', 'Sunset District'): 23,
        ('Bayview', 'Golden Gate Park'): 22,
        ('Bayview', 'Financial District'): 19,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Mission District'): 13,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'Embarcadero'): 11,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Sunset District'): 27,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Financial District'): 9,
        ('Union Square', 'Haight-Ashbury'): 18,
        ('Union Square', 'Mission District'): 14,
        ('Chinatown', 'Marina District'): 12,
        ('Chinatown', 'Embarcadero'): 5,
        ('Chinatown', 'Bayview'): 20,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Sunset District'): 29,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'Haight-Ashbury'): 19,
        ('Chinatown', 'Mission District'): 17,
        ('Sunset District', 'Marina District'): 21,
        ('Sunset District', 'Embarcadero'): 30,
        ('Sunset District', 'Bayview'): 22,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Financial District'): 30,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'Mission District'): 25,
        ('Golden Gate Park', 'Marina District'): 16,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Financial District', 'Marina District'): 15,
        ('Financial District', 'Embarcadero'): 4,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Union Square'): 9,
        ('Financial District', 'Chinatown'): 5,
        ('Financial District', 'Sunset District'): 30,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Haight-Ashbury'): 19,
        ('Financial District', 'Mission District'): 17,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Embarcadero'): 20,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Union Square'): 19,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Financial District'): 21,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Mission District', 'Marina District'): 19,
        ('Mission District', 'Embarcadero'): 19,
        ('Mission District', 'Bayview'): 14,
        ('Mission District', 'Union Square'): 15,
        ('Mission District', 'Chinatown'): 16,
        ('Mission District', 'Sunset District'): 24,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'Financial District'): 15,
        ('Mission District', 'Haight-Ashbury'): 12
    }

    # Create variables for arrival and departure times at each location
    arrival = {loc: Int(f'arrival_{loc}') for loc in locations}
    departure = {loc: Int(f'departure_{loc}') for loc in locations}

    # Starting point: Marina District at 9:00 AM
    s.add(arrival['Marina District'] == 9 * 60)
    s.add(departure['Marina District'] == 9 * 60)

    # Constraints for each location
    for loc in locations:
        if loc == 'Marina District':
            continue  # Already handled
        start, end = locations[loc]
        min_dur = min_durations.get(loc, 0)
        s.add(arrival[loc] >= start)
        s.add(departure[loc] <= end)
        s.add(departure[loc] >= arrival[loc] + min_dur)

    # Define a possible order of visits (this is a simplification; ideally, we'd let Z3 determine the order)
    order = ['Marina District', 'Sunset District', 'Golden Gate Park', 'Union Square', 
             'Chinatown', 'Financial District', 'Embarcadero', 'Bayview', 
             'Mission District', 'Haight-Ashbury']

    # Add travel time constraints between consecutive locations in the order
    for i in range(len(order) - 1):
        loc1 = order[i]
        loc2 = order[i + 1]
        s.add(arrival[loc2] >= departure[loc1] + travel_times[(loc1, loc2)])

    # Check if the schedule is feasible
    if s.check() == sat:
        m = s.model()
        schedule = []
        for loc in order:
            if loc == 'Marina District':
                continue
            arr = m.evaluate(arrival[loc]).as_long()
            dep = m.evaluate(departure[loc]).as_long()
            schedule.append((loc, arr, dep))
        
        # Print the schedule
        print("Feasible schedule found:")
        for loc, arr, dep in schedule:
            print(f"{loc}: {arr//60:02d}:{arr%60:02d} - {dep//60:02d}:{dep%60:02d}")
    else:
        print("No feasible schedule found.")

solve_scheduling()