from z3 import *
from itertools import permutations

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Friends' information
    friends = {
        'Nancy': {'location': 'Chinatown', 'start': 9.5, 'end': 13.5, 'min_duration': 1.5},
        'Mary': {'location': 'Alamo Square', 'start': 7.0, 'end': 21.0, 'min_duration': 1.25},
        'Jessica': {'location': 'Bayview', 'start': 11.25, 'end': 13.75, 'min_duration': 0.75},
        'Rebecca': {'location': 'Fisherman\'s Wharf', 'start': 7.0, 'end': 8.5, 'min_duration': 0.75}
    }

    # Travel times in hours
    travel = {
        ('Financial District', 'Chinatown'): 5/60,
        ('Financial District', 'Alamo Square'): 17/60,
        ('Financial District', 'Bayview'): 19/60,
        ('Financial District', 'Fisherman\'s Wharf'): 10/60,
        ('Chinatown', 'Financial District'): 5/60,
        ('Chinatown', 'Alamo Square'): 17/60,
        ('Chinatown', 'Bayview'): 22/60,
        ('Chinatown', 'Fisherman\'s Wharf'): 8/60,
        ('Alamo Square', 'Financial District'): 17/60,
        ('Alamo Square', 'Chinatown'): 16/60,
        ('Alamo Square', 'Bayview'): 16/60,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19/60,
        ('Bayview', 'Financial District'): 19/60,
        ('Bayview', 'Chinatown'): 18/60,
        ('Bayview', 'Alamo Square'): 16/60,
        ('Bayview', 'Fisherman\'s Wharf'): 25/60,
        ('Fisherman\'s Wharf', 'Financial District'): 11/60,
        ('Fisherman\'s Wharf', 'Chinatown'): 12/60,
        ('Fisherman\'s Wharf', 'Alamo Square'): 20/60,
        ('Fisherman\'s Wharf', 'Bayview'): 26/60
    }

    # Decision variables
    meet = {f: Bool(f'meet_{f}') for f in friends}
    start_time = {f: Real(f'start_{f}') for f in friends}
    end_time = {f: Real(f'end_{f}') for f in friends}
    order = {f: Int(f'order_{f}') for f in friends}  # To track meeting sequence

    # Basic constraints for each friend
    for f in friends:
        info = friends[f]
        s.add(Implies(meet[f], start_time[f] >= info['start']))
        s.add(Implies(meet[f], end_time[f] <= info['end']))
        s.add(Implies(meet[f], end_time[f] - start_time[f] >= info['min_duration']))
        s.add(Implies(meet[f], order[f] >= 1))
        s.add(Implies(Not(meet[f]), order[f] == 0))

    # All active meetings must have unique order numbers
    active_orders = [If(meet[f], order[f], 0) for f in friends]
    s.add(Distinct([o for o in active_orders if o != 0]))

    # Sequence constraints
    for f1 in friends:
        for f2 in friends:
            if f1 != f2:
                # If both meetings happen and f1 comes before f2
                s.add(Implies(And(meet[f1], meet[f2], order[f1] < order[f2]),
                      start_time[f2] >= end_time[f1] + travel[(friends[f1]['location'], friends[f2]['location'])]))

    # Starting point
    first_meeting = [And(meet[f], order[f] == 1) for f in friends]
    s.add(Or(first_meeting))  # At least one meeting must be first
    for f in friends:
        s.add(Implies(And(meet[f], order[f] == 1),
                     start_time[f] >= 9.0 + travel[('Financial District', friends[f]['location'])]))

    # Objective: maximize number of friends met
    s.maximize(Sum([If(meet[f], 1, 0) for f in friends]))

    # Solve
    if s.check() == sat:
        m = s.model()
        print("Optimal schedule found:")
        
        # Get meetings in order
        scheduled = []
        for f in friends:
            if is_true(m.eval(meet[f])):
                scheduled.append((f, m.eval(order[f]).as_long(), 
                                m.eval(start_time[f]), m.eval(end_time[f])))
        
        # Sort by order
        scheduled.sort(key=lambda x: x[1])
        
        # Print schedule
        current_location = 'Financial District'
        current_time = 9.0
        total_met = 0
        
        for f, _, start, end in scheduled:
            travel_time = travel[(current_location, friends[f]['location'])]
            print(f"Travel from {current_location} to {friends[f]['location']} ({travel_time*60:.0f} min)")
            print(f"Meet {f} at {friends[f]['location']} from {start} to {end}")
            current_location = friends[f]['location']
            current_time = float(str(end))
            total_met += 1
        
        print(f"\nTotal friends met: {total_met}")
    else:
        print("No feasible schedule found that meets all constraints.")

solve_scheduling()