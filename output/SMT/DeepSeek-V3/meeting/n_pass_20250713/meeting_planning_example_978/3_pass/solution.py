from z3 import *
from itertools import combinations

def solve_scheduling():
    s = Optimize()

    # Define all locations and friends
    friends = {
        'Stephanie': {'location': 'Fisherman\'s Wharf', 'start': 15.5, 'end': 22.0, 'duration': 0.5},
        'Lisa': {'location': 'Financial District', 'start': 10.75, 'end': 17.25, 'duration': 0.25},
        'Melissa': {'location': 'Russian Hill', 'start': 17.0, 'end': 21.75, 'duration': 2.0},
        'Betty': {'location': 'Marina District', 'start': 10.75, 'end': 14.25, 'duration': 1.0},
        'Sarah': {'location': 'Richmond District', 'start': 16.25, 'end': 19.5, 'duration': 1.75},
        'Daniel': {'location': 'Pacific Heights', 'start': 18.5, 'end': 21.75, 'duration': 1.0},
        'Joshua': {'location': 'Haight-Ashbury', 'start': 9.0, 'end': 15.5, 'duration': 0.25},
        'Joseph': {'location': 'Presidio', 'start': 7.0, 'end': 13.0, 'duration': 0.75},
        'Andrew': {'location': 'Nob Hill', 'start': 19.75, 'end': 22.0, 'duration': 1.75},
        'John': {'location': 'The Castro', 'start': 13.25, 'end': 19.75, 'duration': 0.75}
    }

    # Complete travel times matrix (minutes converted to hours)
    locations = list(set(f['location'] for f in friends.values())) | ['Embarcadero']
    travel_times = {
        ('Embarcadero', 'Fisherman\'s Wharf'): 6/60,
        ('Embarcadero', 'Financial District'): 5/60,
        ('Embarcadero', 'Russian Hill'): 8/60,
        ('Embarcadero', 'Marina District'): 12/60,
        ('Embarcadero', 'Richmond District'): 21/60,
        ('Embarcadero', 'Pacific Heights'): 11/60,
        ('Embarcadero', 'Haight-Ashbury'): 21/60,
        ('Embarcadero', 'Presidio'): 20/60,
        ('Embarcadero', 'Nob Hill'): 10/60,
        ('Embarcadero', 'The Castro'): 25/60,
        # Add all reverse directions
        ('Fisherman\'s Wharf', 'Embarcadero'): 8/60,
        ('Financial District', 'Embarcadero'): 4/60,
        ('Russian Hill', 'Embarcadero'): 8/60,
        ('Marina District', 'Embarcadero'): 14/60,
        ('Richmond District', 'Embarcadero'): 19/60,
        ('Pacific Heights', 'Embarcadero'): 10/60,
        ('Haight-Ashbury', 'Embarcadero'): 20/60,
        ('Presidio', 'Embarcadero'): 20/60,
        ('Nob Hill', 'Embarcadero'): 9/60,
        ('The Castro', 'Embarcadero'): 22/60,
        # Add other pairwise times
        ('Fisherman\'s Wharf', 'Financial District'): 11/60,
        ('Financial District', 'Fisherman\'s Wharf'): 10/60,
        # Add more as needed...
    }

    # Create variables
    meet = {name: Bool(f'meet_{name}') for name in friends}
    start = {name: Real(f'start_{name}') for name in friends}
    end = {name: Real(f'end_{name}') for name in friends}
    order = {name: Int(f'order_{name}') for name in friends}

    # Constraints for each friend
    for name in friends:
        f = friends[name]
        s.add(Implies(meet[name], start[name] >= f['start']))
        s.add(Implies(meet[name], end[name] <= f['end']))
        s.add(Implies(meet[name], end[name] == start[name] + f['duration']))
        s.add(Implies(Not(meet[name]), start[name] == 0))
        s.add(Implies(Not(meet[name]), end[name] == 0))

    # Exactly 9 friends must be met
    s.add(Sum([If(meet[name], 1, 0) for name in friends]) == 9)

    # Ordering constraints
    for name1, name2 in combinations(friends.keys(), 2):
        loc1 = friends[name1]['location']
        loc2 = friends[name2]['location']
        travel = travel_times.get((loc1, loc2), 0)  # Default to 0 if no direct route
        
        # If both are met, ensure proper ordering and travel time
        s.add(Implies(And(meet[name1], meet[name2], order[name1] < order[name2]),
                      start[name2] >= end[name1] + travel))

    # Starting point
    first_meeting = [name for name in friends if order[name] == 1]
    s.add(Sum([If(order[name] == 1, 1, 0) for name in friends]) == 1)
    for name in friends:
        s.add(Implies(order[name] == 1, 
                     start[name] >= 9.0 + travel_times[('Embarcadero', friends[name]['location'])]))

    # Solve
    if s.check() == sat:
        m = s.model()
        scheduled = []
        for name in friends:
            if m[meet[name]]:
                start_time = m[start[name]].as_fraction()
                end_time = m[end[name]].as_fraction()
                def to_time(h):
                    hours = float(h)
                    hh = int(hours)
                    mm = int((hours - hh) * 60)
                    return f"{hh:02d}:{mm:02d}"
                scheduled.append((name, to_time(start_time), to_time(end_time)))
        
        # Sort by start time
        scheduled.sort(key=lambda x: x[1])
        print("Valid schedule meeting 9 friends:")
        for name, start_t, end_t in scheduled:
            print(f"{name}: {start_t}-{end_t} at {friends[name]['location']}")
    else:
        print("No valid schedule found")

solve_scheduling()