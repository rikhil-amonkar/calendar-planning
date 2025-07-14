from z3 import *

def solve_scheduling():
    s = Solver()

    # Friends data with locations, time windows and durations
    friends = {
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

    # Travel times in hours between locations
    travel_times = {
        ('Bayview', 'Fisherman\'s Wharf'): 25/60,
        ('Fisherman\'s Wharf', 'Nob Hill'): 11/60,
        ('Nob Hill', 'Pacific Heights'): 8/60,
        ('Pacific Heights', 'North Beach'): 9/60,
        ('North Beach', 'Chinatown'): 6/60,
        ('Chinatown', 'Haight-Ashbury'): 19/60,
        ('Haight-Ashbury', 'Alamo Square'): 5/60,
        ('Alamo Square', 'Union Square'): 14/60,
        ('Union Square', 'Golden Gate Park'): 22/60
    }

    # Variables
    arrival = {name: Real(f'arrival_{name}') for name in friends}
    departure = {name: Real(f'departure_{name}') for name in friends}
    meet = {name: Bool(f'meet_{name}') for name in friends}

    # Starting point
    current_time = 9.0  # 9:00 AM from Bayview

    # We'll skip Jessica to meet exactly 8 friends
    s.add(Not(meet['Jessica']))

    # Constraints for each friend
    for name in friends:
        if name != 'Jessica':
            s.add(Implies(meet[name], arrival[name] >= friends[name]['start']))
            s.add(Implies(meet[name], departure[name] == arrival[name] + friends[name]['duration']))
            s.add(Implies(meet[name], departure[name] <= friends[name]['end']))
        else:
            s.add(Not(meet[name]))

    # Ensure exactly 8 friends are met
    s.add(Sum([If(meet[name], 1, 0) for name in friends]) == 8)

    # Define a logical visiting order
    visit_order = ['Richard', 'Elizabeth', 'Anthony', 'Brian', 'Kenneth', 'Ashley', 'Kimberly', 'Deborah']

    # Add travel time constraints
    prev_location = 'Bayview'
    for i in range(len(visit_order)):
        name = visit_order[i]
        if i == 0:
            s.add(Implies(meet[name], arrival[name] >= current_time + travel_times[(prev_location, friends[name]['location'])]))
        else:
            prev_name = visit_order[i-1]
            s.add(Implies(And(meet[prev_name], meet[name]),
                  arrival[name] >= departure[prev_name] + travel_times[(friends[prev_name]['location'], friends[name]['location'])]))
        prev_location = friends[name]['location']

    if s.check() == sat:
        m = s.model()
        print("Feasible schedule found (meeting exactly 8 friends):")
        for name in visit_order:
            if is_true(m[meet[name]]):
                arr = m[arrival[name]].as_fraction()
                dep = m[departure[name]].as_fraction()
                print(f"{name}: {float(arr):.2f}-{float(dep):.2f} at {friends[name]['location']}")
    else:
        print("No feasible schedule found")

solve_scheduling()