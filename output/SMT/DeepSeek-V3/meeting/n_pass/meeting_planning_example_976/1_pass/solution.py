from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Friends and their details
    friends = {
        'Matthew': {'location': 'Bayview', 'start': 19.25, 'end': 22.0, 'min_duration': 2.0},
        'Karen': {'location': 'Chinatown', 'start': 19.25, 'end': 21.25, 'min_duration': 1.5},
        'Sarah': {'location': 'Alamo Square', 'start': 20.0, 'end': 21.75, 'min_duration': 1.75},
        'Jessica': {'location': 'Nob Hill', 'start': 16.5, 'end': 18.75, 'min_duration': 2.0},
        'Stephanie': {'location': 'Presidio', 'start': 7.5, 'end': 10.25, 'min_duration': 1.0},
        'Mary': {'location': 'Union Square', 'start': 16.75, 'end': 21.5, 'min_duration': 1.0},
        'Charles': {'location': 'The Castro', 'start': 16.5, 'end': 22.0, 'min_duration': 1.75},
        'Nancy': {'location': 'North Beach', 'start': 14.75, 'end': 20.0, 'min_duration': 0.25},
        'Thomas': {'location': 'Fisherman\'s Wharf', 'start': 13.5, 'end': 19.0, 'min_duration': 0.5},
        'Brian': {'location': 'Marina District', 'start': 12.25, 'end': 18.0, 'min_duration': 1.0}
    }

    # Travel times (simplified as a dictionary of dictionaries)
    travel_times = {
        'Embarcadero': {
            'Bayview': 21/60, 'Chinatown': 7/60, 'Alamo Square': 19/60, 'Nob Hill': 10/60,
            'Presidio': 20/60, 'Union Square': 10/60, 'The Castro': 25/60, 'North Beach': 5/60,
            'Fisherman\'s Wharf': 6/60, 'Marina District': 12/60
        },
        'Bayview': {
            'Embarcadero': 19/60, 'Chinatown': 19/60, 'Alamo Square': 16/60, 'Nob Hill': 20/60,
            'Presidio': 32/60, 'Union Square': 18/60, 'The Castro': 19/60, 'North Beach': 22/60,
            'Fisherman\'s Wharf': 25/60, 'Marina District': 27/60
        },
        'Chinatown': {
            'Embarcadero': 5/60, 'Bayview': 20/60, 'Alamo Square': 17/60, 'Nob Hill': 9/60,
            'Presidio': 19/60, 'Union Square': 7/60, 'The Castro': 22/60, 'North Beach': 3/60,
            'Fisherman\'s Wharf': 8/60, 'Marina District': 12/60
        },
        'Alamo Square': {
            'Embarcadero': 16/60, 'Bayview': 16/60, 'Chinatown': 15/60, 'Nob Hill': 11/60,
            'Presidio': 17/60, 'Union Square': 14/60, 'The Castro': 8/60, 'North Beach': 15/60,
            'Fisherman\'s Wharf': 19/60, 'Marina District': 15/60
        },
        'Nob Hill': {
            'Embarcadero': 9/60, 'Bayview': 19/60, 'Chinatown': 6/60, 'Alamo Square': 11/60,
            'Presidio': 17/60, 'Union Square': 7/60, 'The Castro': 17/60, 'North Beach': 8/60,
            'Fisherman\'s Wharf': 10/60, 'Marina District': 11/60
        },
        'Presidio': {
            'Embarcadero': 20/60, 'Bayview': 31/60, 'Chinatown': 21/60, 'Alamo Square': 19/60,
            'Nob Hill': 18/60, 'Union Square': 22/60, 'The Castro': 21/60, 'North Beach': 18/60,
            'Fisherman\'s Wharf': 19/60, 'Marina District': 11/60
        },
        'Union Square': {
            'Embarcadero': 11/60, 'Bayview': 15/60, 'Chinatown': 7/60, 'Alamo Square': 15/60,
            'Nob Hill': 9/60, 'Presidio': 24/60, 'The Castro': 17/60, 'North Beach': 10/60,
            'Fisherman\'s Wharf': 15/60, 'Marina District': 18/60
        },
        'The Castro': {
            'Embarcadero': 22/60, 'Bayview': 19/60, 'Chinatown': 22/60, 'Alamo Square': 8/60,
            'Nob Hill': 16/60, 'Presidio': 20/60, 'Union Square': 19/60, 'North Beach': 20/60,
            'Fisherman\'s Wharf': 24/60, 'Marina District': 21/60
        },
        'North Beach': {
            'Embarcadero': 6/60, 'Bayview': 25/60, 'Chinatown': 6/60, 'Alamo Square': 16/60,
            'Nob Hill': 7/60, 'Presidio': 17/60, 'Union Square': 7/60, 'The Castro': 23/60,
            'Fisherman\'s Wharf': 5/60, 'Marina District': 9/60
        },
        'Fisherman\'s Wharf': {
            'Embarcadero': 8/60, 'Bayview': 26/60, 'Chinatown': 12/60, 'Alamo Square': 21/60,
            'Nob Hill': 11/60, 'Presidio': 17/60, 'Union Square': 13/60, 'The Castro': 27/60,
            'North Beach': 6/60, 'Marina District': 9/60
        },
        'Marina District': {
            'Embarcadero': 14/60, 'Bayview': 27/60, 'Chinatown': 15/60, 'Alamo Square': 15/60,
            'Nob Hill': 12/60, 'Presidio': 10/60, 'Union Square': 16/60, 'The Castro': 22/60,
            'North Beach': 11/60, 'Fisherman\'s Wharf': 10/60
        }
    }

    # Variables for each friend: arrival time, departure time, and whether they are met
    vars = {}
    for name in friends:
        vars[name] = {
            'arrival': Real(f'arrival_{name}'),
            'departure': Real(f'departure_{name}'),
            'met': Bool(f'met_{name}')
        }

    # Current location starts at Embarcadero at 9:00 AM (9.0)
    current_time = 9.0
    current_location = 'Embarcadero'

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        loc = friend['location']
        start = friend['start']
        end = friend['end']
        min_duration = friend['min_duration']
        arrival = vars[name]['arrival']
        departure = vars[name]['departure']
        met = vars[name]['met']

        # If met, arrival and departure must be within friend's availability
        s.add(Implies(met, And(arrival >= start, departure <= end, departure - arrival >= min_duration))
        # If not met, arrival and departure are unconstrained
        s.add(Implies(Not(met), And(arrival == 0, departure == 0)))

    # Sequence constraints: ensure travel times are respected between consecutive meetings
    # This is a simplified approach; a more precise approach would model the order of visits
    # Here, we assume the order is arbitrary but travel times must be respected between any two meetings
    for name1 in friends:
        for name2 in friends:
            if name1 == name2:
                continue
            loc1 = friends[name1]['location']
            loc2 = friends[name2]['location']
            travel_time = travel_times[loc1][loc2]
            s.add(Implies(And(vars[name1]['met'], vars[name2]['met']),
                  vars[name2]['arrival'] >= vars[name1]['departure'] + travel_time))

    # Initial constraint: first meeting must be after travel from Embarcadero
    for name in friends:
        loc = friends[name]['location']
        travel_time = travel_times[current_location][loc]
        s.add(Implies(vars[name]['met'], vars[name]['arrival'] >= current_time + travel_time))

    # Objective: maximize the number of friends met
    objective = Sum([If(vars[name]['met'], 1, 0) for name in friends])
    s.maximize(objective)

    # Solve
    if s.check() == sat:
        m = s.model()
        met_friends = []
        for name in friends:
            if is_true(m.evaluate(vars[name]['met'])):
                arrival = m.evaluate(vars[name]['arrival'])
                departure = m.evaluate(vars[name]['departure'])
                met_friends.append((name, float(arrival.as_fraction()), float(departure.as_fraction())))
        met_friends.sort(key=lambda x: x[1])  # Sort by arrival time
        return met_friends
    else:
        return None

# Run the solver
schedule = solve_scheduling()

# Print the solution
print("SOLUTION:")
if schedule:
    print("Optimal schedule meeting the following friends:")
    for name, arrival, departure in schedule:
        print(f"- {name}: from {arrival:.2f} to {departure:.2f}")
else:
    print("No feasible schedule found.")