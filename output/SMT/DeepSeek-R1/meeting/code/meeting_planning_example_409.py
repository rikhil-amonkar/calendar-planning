from z3 import *
from itertools import combinations

def solve_scheduling():
    travel_times = {
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Nob Hill'): 11,
        ('Fisherman\'s Wharf', 'Marina District'): 9,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Golden Gate Park'): 22,
        ('Bayview', 'Nob Hill'): 20,
        ('Bayview', 'Marina District'): 25,
        ('Bayview', 'Embarcadero'): 19,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Golden Gate Park', 'Nob Hill'): 20,
        ('Golden Gate Park', 'Marina District'): 16,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Nob Hill', 'Fisherman\'s Wharf'): 11,
        ('Nob Hill', 'Bayview'): 19,
        ('Nob Hill', 'Golden Gate Park'): 17,
        ('Nob Hill', 'Marina District'): 11,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Marina District', 'Fisherman\'s Wharf'): 10,
        ('Marina District', 'Bayview'): 27,
        ('Marina District', 'Golden Gate Park'): 18,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Embarcadero'): 14,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Marina District'): 12,
    }

    friends = [
        {'name': 'Thomas', 'location': 'Bayview',
         'available_start': 15*60 + 30, 'available_end': 18*60 + 30,
         'duration': 120},
        {'name': 'Stephanie', 'location': 'Golden Gate Park',
         'available_start': 18*60 + 30, 'available_end': 21*60 + 45,
         'duration': 30},
        {'name': 'Laura', 'location': 'Nob Hill',
         'available_start': 8*60 + 45, 'available_end': 16*60 + 15,
         'duration': 30},
        {'name': 'Betty', 'location': 'Marina District',
         'available_start': 18*60 + 45, 'available_end': 21*60 + 45,
         'duration': 45},
        {'name': 'Patricia', 'location': 'Embarcadero',
         'available_start': 17*60 + 30, 'available_end': 22*60,
         'duration': 45}
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
        travel = travel_times[('Fisherman\'s Wharf', f['location'])]
        s.add(Implies(meet, start >= 540 + travel))  # 9:00 AM arrival + travel
        s.add(Implies(meet, start >= f['available_start']))
        s.add(Implies(meet, end == start + f['duration']))
        s.add(Implies(meet, end <= f['available_end']))

    # Pairwise constraints for travel times between locations
    for a, b in combinations(friends, 2):
        a_to_b = travel_times[(a['location'], b['location'])]
        b_to_a = travel_times[(b['location'], a['location'])]
        s.add(Implies(And(a['meet'], b['meet']),
                    Or(a['end'] + a_to_b <= b['start'],
                       b['end'] + b_to_a <= a['start'])))

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