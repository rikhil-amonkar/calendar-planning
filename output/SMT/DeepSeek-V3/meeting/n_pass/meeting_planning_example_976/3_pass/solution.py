from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

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

    # Travel times (in hours)
    travel_times = {
        'Embarcadero': {'Bayview': 21/60, 'Chinatown': 7/60, 'Alamo Square': 19/60, 'Nob Hill': 10/60,
                        'Presidio': 20/60, 'Union Square': 10/60, 'The Castro': 25/60, 'North Beach': 5/60,
                        'Fisherman\'s Wharf': 6/60, 'Marina District': 12/60},
        'Bayview': {'Embarcadero': 19/60, 'Chinatown': 19/60, 'Alamo Square': 16/60, 'Nob Hill': 20/60,
                    'Presidio': 32/60, 'Union Square': 18/60, 'The Castro': 19/60, 'North Beach': 22/60,
                    'Fisherman\'s Wharf': 25/60, 'Marina District': 27/60},
        'Chinatown': {'Embarcadero': 5/60, 'Bayview': 20/60, 'Alamo Square': 17/60, 'Nob Hill': 9/60,
                      'Presidio': 19/60, 'Union Square': 7/60, 'The Castro': 22/60, 'North Beach': 3/60,
                      'Fisherman\'s Wharf': 8/60, 'Marina District': 12/60},
        'Alamo Square': {'Embarcadero': 16/60, 'Bayview': 16/60, 'Chinatown': 15/60, 'Nob Hill': 11/60,
                         'Presidio': 17/60, 'Union Square': 14/60, 'The Castro': 8/60, 'North Beach': 15/60,
                         'Fisherman\'s Wharf': 19/60, 'Marina District': 15/60},
        'Nob Hill': {'Embarcadero': 9/60, 'Bayview': 19/60, 'Chinatown': 6/60, 'Alamo Square': 11/60,
                     'Presidio': 17/60, 'Union Square': 7/60, 'The Castro': 17/60, 'North Beach': 8/60,
                     'Fisherman\'s Wharf': 10/60, 'Marina District': 11/60},
        'Presidio': {'Embarcadero': 20/60, 'Bayview': 31/60, 'Chinatown': 21/60, 'Alamo Square': 19/60,
                     'Nob Hill': 18/60, 'Union Square': 22/60, 'The Castro': 21/60, 'North Beach': 18/60,
                     'Fisherman\'s Wharf': 19/60, 'Marina District': 11/60},
        'Union Square': {'Embarcadero': 11/60, 'Bayview': 15/60, 'Chinatown': 7/60, 'Alamo Square': 15/60,
                         'Nob Hill': 9/60, 'Presidio': 24/60, 'The Castro': 17/60, 'North Beach': 10/60,
                         'Fisherman\'s Wharf': 15/60, 'Marina District': 18/60},
        'The Castro': {'Embarcadero': 22/60, 'Bayview': 19/60, 'Chinatown': 22/60, 'Alamo Square': 8/60,
                       'Nob Hill': 16/60, 'Presidio': 20/60, 'Union Square': 19/60, 'North Beach': 20/60,
                       'Fisherman\'s Wharf': 24/60, 'Marina District': 21/60},
        'North Beach': {'Embarcadero': 6/60, 'Bayview': 25/60, 'Chinatown': 6/60, 'Alamo Square': 16/60,
                        'Nob Hill': 7/60, 'Presidio': 17/60, 'Union Square': 7/60, 'The Castro': 23/60,
                        'Fisherman\'s Wharf': 5/60, 'Marina District': 9/60},
        'Fisherman\'s Wharf': {'Embarcadero': 8/60, 'Bayview': 26/60, 'Chinatown': 12/60, 'Alamo Square': 21/60,
                               'Nob Hill': 11/60, 'Presidio': 17/60, 'Union Square': 13/60, 'The Castro': 27/60,
                               'North Beach': 6/60, 'Marina District': 9/60},
        'Marina District': {'Embarcadero': 14/60, 'Bayview': 27/60, 'Chinatown': 15/60, 'Alamo Square': 15/60,
                            'Nob Hill': 12/60, 'Presidio': 10/60, 'Union Square': 16/60, 'The Castro': 22/60,
                            'North Beach': 11/60, 'Fisherman\'s Wharf': 10/60}
    }

    # Create variables
    arrival = {name: Real(f'arrival_{name}') for name in friends}
    departure = {name: Real(f'departure_{name}') for name in friends}
    met = {name: Bool(f'met_{name}') for name in friends}
    order = {name: Int(f'order_{name}') for name in friends}

    # Current location and time
    current_time = 9.0  # 9:00 AM
    current_location = 'Embarcadero'

    # Basic constraints for each friend
    for name in friends:
        friend = friends[name]
        s.add(Implies(met[name], 
                     And(arrival[name] >= friend['start'],
                         departure[name] <= friend['end'],
                         departure[name] - arrival[name] >= friend['min_duration'])))
        s.add(Implies(Not(met[name]), 
                     And(arrival[name] == 0, departure[name] == 0, order[name] == -1)))

    # Order constraints
    for name in friends:
        s.add(Implies(met[name], order[name] >= 0))

    # Sequence constraints
    for name1 in friends:
        for name2 in friends:
            if name1 == name2:
                continue
            loc1 = friends[name1]['location']
            loc2 = friends[name2]['location']
            travel = travel_times[loc1][loc2]
            s.add(Implies(And(met[name1], met[name2], order[name1] < order[name2]),
                         arrival[name2] >= departure[name1] + travel))

    # Initial constraint
    for name in friends:
        loc = friends[name]['location']
        travel = travel_times[current_location][loc]
        s.add(Implies(And(met[name], order[name] == 0),
                     arrival[name] >= current_time + travel))

    # All met friends must have unique order numbers
    s.add(Distinct([order[name] for name in friends if met[name]]))
    for name in friends:
        s.add(Implies(met[name], order[name] >= 0))
        s.add(Implies(Not(met[name]), order[name] == -1))

    # Maximize number of friends met
    s.maximize(Sum([If(met[name], 1, 0) for name in friends]))

    if s.check() == sat:
        m = s.model()
        schedule = []
        for name in friends:
            if is_true(m.evaluate(met[name])):
                a = m.evaluate(arrival[name])
                d = m.evaluate(departure[name])
                o = m.evaluate(order[name])
                # Convert Z3 rational numbers to float
                a_val = float(a.numerator_as_long())/float(a.denominator_as_long()) if is_rational_value(a) else float(str(a))
                d_val = float(d.numerator_as_long())/float(d.denominator_as_long()) if is_rational_value(d) else float(str(d))
                schedule.append((name, a_val, d_val, o.as_long()))
        # Sort by order
        schedule.sort(key=lambda x: x[3])
        return schedule
    else:
        return None

# Run the solver
schedule = solve_scheduling()

# Print the solution
print("SOLUTION:")
if schedule:
    print("Optimal schedule meeting the following friends in order:")
    for name, arrival, departure, order in schedule:
        print(f"{order+1}. {name}: {arrival:.2f} - {departure:.2f} at {friends[name]['location']}")
else:
    print("No feasible schedule found.")