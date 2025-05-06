from z3 import *
from itertools import combinations

def solve_scheduling():
    travel_times = {
        ('Union Square', 'Nob Hill'): 9,
        ('Union Square', 'Haight-Ashbury'): 18,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Marina District'): 18,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'Haight-Ashbury'): 13,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Marina District'): 11,
        ('Haight-Ashbury', 'Union Square'): 17,
        ('Haight-Ashbury', 'Nob Hill'): 15,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Nob Hill'): 8,
        ('Chinatown', 'Haight-Ashbury'): 19,
        ('Chinatown', 'Marina District'): 12,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'Chinatown'): 16,
    }

    friends = [
        {'name': 'Karen', 'location': 'Nob Hill', 
         'available_start': 21*60+15, 'available_end': 21*60+45, 
         'duration': 30},
        {'name': 'Joseph', 'location': 'Haight-Ashbury', 
         'available_start': 12*60+30, 'available_end': 19*60+45, 
         'duration': 90},
        {'name': 'Sandra', 'location': 'Chinatown', 
         'available_start': 7*60+15, 'available_end': 19*60+15, 
         'duration': 75},
        {'name': 'Nancy', 'location': 'Marina District', 
         'available_start': 11*60, 'available_end': 20*60+15, 
         'duration': 105}
    ]

    # Initialize Z3 variables
    for f in friends:
        name = f['name']
        f['meet'] = Bool(f'meet_{name}')
        f['start'] = Int(f'start_{name}')
        f['end'] = Int(f'end_{name}')

    s = Optimize()

    # Individual constraints for each friend
    for f in friends:
        meet = f['meet']
        start = f['start']
        end = f['end']
        travel = travel_times[('Union Square', f['location'])]
        s.add(Implies(meet, start >= 540 + travel))  # Arrival + travel
        s.add(Implies(meet, start >= f['available_start']))
        s.add(Implies(meet, end == start + f['duration']))
        s.add(Implies(meet, end <= f['available_end']))

    # Pairwise constraints for travel times
    for (a, b) in combinations(friends, 2):
        a_to_b = travel_times[(a['location'], b['location'])]
        b_to_a = travel_times[(b['location'], a['location'])]
        s.add(Implies(And(a['meet'], b['meet']),
                    Or(a['start'] >= b['end'] + b_to_a,
                       b['start'] >= a['end'] + a_to_a)))

    # Maximize number of friends met
    total_met = Sum([If(f['meet'], 1, 0) for f in friends])
    s.maximize(total_met)

    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        for f in friends:
            if m.evaluate(f['meet']):
                start = m.evaluate(f['start']).as_long()
                end = start + f['duration']
                print(f"{f['name']}: {start//60:02d}:{start%60:02d} - {end//60:02d}:{end%60:02d}")
            else:
                print(f"{f['name']}: Not met")
    else:
        print("No valid schedule found")

solve_scheduling()