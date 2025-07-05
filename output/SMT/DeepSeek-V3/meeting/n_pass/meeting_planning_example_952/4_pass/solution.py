from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their locations, available times, and desired meeting durations
    friends = {
        'Matthew': {'location': 'Presidio', 'start': 8.25, 'end': 9.0, 'duration': 0.25},
        'Richard': {'location': 'Fisherman\'s Wharf', 'start': 11.0, 'end': 12.75, 'duration': 1.0},
        'Elizabeth': {'location': 'Nob Hill', 'start': 11.75, 'end': 18.5, 'duration': 1.25},
        'Anthony': {'location': 'Pacific Heights', 'start': 14.25, 'end': 16.0, 'duration': 0.5},
        'Brian': {'location': 'North Beach', 'start': 13.0, 'end': 19.0, 'duration': 1.5},
        'Kenneth': {'location': 'Chinatown', 'start': 13.75, 'end': 19.5, 'duration': 1.75},
        'Ashley': {'location': 'Haight-Ashbury', 'start': 15.0, 'end': 20.5, 'duration': 1.5},
        'Kimberly': {'location': 'Alamo Square', 'start': 17.5, 'end': 21.25, 'duration': 0.75},
        'Deborah': {'location': 'Union Square', 'start': 17.5, 'end': 22.0, 'duration': 1.0},
        'Jessica': {'location': 'Golden Gate Park', 'start': 20.0, 'end': 21.75, 'duration': 1.75}
    }

    # Define all possible travel times (in hours)
    travel_times = {
        ('Bayview', 'Fisherman\'s Wharf'): 25/60,
        ('Bayview', 'Nob Hill'): 20/60,
        ('Bayview', 'Pacific Heights'): 23/60,
        ('Bayview', 'North Beach'): 22/60,
        ('Bayview', 'Chinatown'): 19/60,
        ('Bayview', 'Haight-Ashbury'): 19/60,
        ('Bayview', 'Alamo Square'): 16/60,
        ('Bayview', 'Union Square'): 18/60,
        ('Fisherman\'s Wharf', 'Nob Hill'): 11/60,
        ('Nob Hill', 'Pacific Heights'): 8/60,
        ('Pacific Heights', 'North Beach'): 9/60,
        ('North Beach', 'Chinatown'): 6/60,
        ('Chinatown', 'Haight-Ashbury'): 19/60,
        ('Haight-Ashbury', 'Alamo Square'): 5/60,
        ('Alamo Square', 'Union Square'): 14/60,
        ('Union Square', 'Golden Gate Park'): 22/60
    }

    # Variables for arrival and departure times at each friend's location
    arrival = {name: Real(f'arrival_{name}') for name in friends}
    departure = {name: Real(f'departure_{name}') for name in friends}

    # Binary variables to indicate whether a friend is met
    meet = {name: Bool(f'meet_{name}') for name in friends}

    # Initial constraints: start at Bayview at 9:00 AM
    current_time = 9.0  # 9:00 AM

    # Since we must meet exactly 8 people, we'll skip one friend
    # We'll skip Matthew (Presidio) because it's not feasible to meet him at 8:15 AM
    s.add(Not(meet['Matthew']))
    s.add(Not(meet['Jessica']))  # Skip Jessica to meet exactly 8 friends

    # Constraints for each friend
    for name in friends:
        if name not in ['Matthew', 'Jessica']:
            # If meeting the friend, ensure arrival and departure times are within their window
            s.add(Implies(meet[name], arrival[name] >= friends[name]['start']))
            s.add(Implies(meet[name], departure[name] == arrival[name] + friends[name]['duration']))
            s.add(Implies(meet[name], departure[name] <= friends[name]['end']))
        else:
            # Ensure Matthew and Jessica are not met
            s.add(Not(meet[name]))

    # Ensure exactly 8 friends are met
    s.add(Sum([If(meet[name], 1, 0) for name in friends]) == 8)

    # Define the order of visits (this can be optimized further)
    visit_order = ['Richard', 'Elizabeth', 'Anthony', 'Brian', 'Kenneth', 'Ashley', 'Kimberly', 'Deborah']

    # Constraints for the order of visits
    prev_location = 'Bayview'
    for i in range(len(visit_order)):
        name = visit_order[i]
        # Ensure arrival is after previous departure plus travel time
        if i == 0:
            s.add(Implies(meet[name], arrival[name] >= current_time + travel_times[(prev_location, friends[name]['location'])]))
        else:
            prev_name = visit_order[i-1]
            s.add(Implies(And(meet[prev_name], meet[name]), 
                  arrival[name] >= departure[prev_name] + travel_times[(friends[prev_name]['location'], friends[name]['location'])]))
        prev_location = friends[name]['location']

    # Check if the schedule is feasible
    if s.check() == sat:
        m = s.model()
        print("Feasible schedule found (meeting exactly 8 friends):")
        for name in visit_order:
            if is_true(m[meet[name]]):
                # Convert fractional hours to HH:MM format
                arrival_time = m[arrival[name]].as_fraction()
                departure_time = m[departure[name]].as_fraction()
                arrival_hh = int(float(arrival_time))
                arrival_mm = int((float(arrival_time) - arrival_hh) * 60)
                departure_hh = int(float(departure_time))
                departure_mm = int((float(departure_time) - departure_hh) * 60)
                print(f"{name}: Arrival at {arrival_hh:02d}:{arrival_mm:02d}, Departure at {departure_hh:02d}:{departure_mm:02d}")
    else:
        print("No feasible schedule found.")

solve_scheduling()