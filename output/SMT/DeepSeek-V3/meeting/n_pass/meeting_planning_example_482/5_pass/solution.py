from z3 import *

def solve_scheduling():
    s = Optimize()

    # Friends data
    friends = {
        'Stephanie': {'location': 'Mission District', 'start': 8.25, 'end': 13.75, 'min_duration': 1.5},
        'Sandra': {'location': 'Bayview', 'start': 13.0, 'end': 19.5, 'min_duration': 0.25},
        'Richard': {'location': 'Pacific Heights', 'start': 7.25, 'end': 10.25, 'min_duration': 1.25},
        'Brian': {'location': 'Russian Hill', 'start': 12.25, 'end': 16.0, 'min_duration': 2.0},
        'Jason': {'location': "Fisherman's Wharf", 'start': 8.5, 'end': 17.75, 'min_duration': 1.0}
    }

    # Travel times in hours
    travel_times = {
        ('Haight-Ashbury', 'Mission District'): 11/60,
        ('Haight-Ashbury', 'Bayview'): 18/60,
        ('Haight-Ashbury', 'Pacific Heights'): 12/60,
        ('Haight-Ashbury', 'Russian Hill'): 17/60,
        ('Haight-Ashbury', "Fisherman's Wharf"): 23/60,
        ('Mission District', 'Bayview'): 15/60,
        ('Mission District', 'Pacific Heights'): 16/60,
        ('Mission District', 'Russian Hill'): 15/60,
        ('Mission District', "Fisherman's Wharf"): 22/60,
        ('Bayview', 'Mission District'): 13/60,
        ('Bayview', 'Russian Hill'): 23/60,
        ('Bayview', "Fisherman's Wharf"): 25/60,
        ('Pacific Heights', 'Mission District'): 15/60,
        ('Pacific Heights', 'Russian Hill'): 7/60,
        ('Pacific Heights', "Fisherman's Wharf"): 13/60,
        ('Russian Hill', 'Mission District'): 16/60,
        ('Russian Hill', 'Bayview'): 23/60,
        ('Russian Hill', "Fisherman's Wharf"): 7/60,
        ("Fisherman's Wharf", 'Mission District'): 22/60,
        ("Fisherman's Wharf", 'Russian Hill'): 7/60
    }

    # Variables
    meet = {name: Bool(f'meet_{name}') for name in friends}
    start = {name: Real(f'start_{name}') for name in friends}
    end = {name: Real(f'end_{name}') for name in friends}

    current_time = 9.0  # starting at Haight-Ashbury at 9:00 AM
    current_location = 'Haight-Ashbury'

    # Basic constraints for each friend
    for name in friends:
        data = friends[name]
        s.add(Implies(meet[name], start[name] >= data['start']))
        s.add(Implies(meet[name], end[name] <= data['end']))
        s.add(Implies(meet[name], end[name] == start[name] + data['min_duration']))

    # Define possible meeting sequences
    # Option 1: Richard -> Stephanie -> Brian -> Sandra -> Jason
    option1 = And(
        meet['Richard'],
        meet['Stephanie'],
        meet['Brian'],
        meet['Sandra'],
        meet['Jason'],
        start['Richard'] >= current_time + travel_times[(current_location, 'Pacific Heights')],
        start['Stephanie'] >= end['Richard'] + travel_times[('Pacific Heights', 'Mission District')],
        start['Brian'] >= end['Stephanie'] + travel_times[('Mission District', 'Russian Hill')],
        start['Sandra'] >= end['Brian'] + travel_times[('Russian Hill', 'Bayview')],
        start['Jason'] >= end['Sandra'] + travel_times[('Bayview', "Fisherman's Wharf")]
    )

    # Option 2: Stephanie -> Brian -> Sandra -> Jason
    option2 = And(
        Not(meet['Richard']),
        meet['Stephanie'],
        meet['Brian'],
        meet['Sandra'],
        meet['Jason'],
        start['Stephanie'] >= current_time + travel_times[(current_location, 'Mission District')],
        start['Brian'] >= end['Stephanie'] + travel_times[('Mission District', 'Russian Hill')],
        start['Sandra'] >= end['Brian'] + travel_times[('Russian Hill', 'Bayview')],
        start['Jason'] >= end['Sandra'] + travel_times[('Bayview', "Fisherman's Wharf")]
    )

    # Option 3: Richard -> Brian -> Sandra -> Jason
    option3 = And(
        meet['Richard'],
        Not(meet['Stephanie']),
        meet['Brian'],
        meet['Sandra'],
        meet['Jason'],
        start['Richard'] >= current_time + travel_times[(current_location, 'Pacific Heights')],
        start['Brian'] >= end['Richard'] + travel_times[('Pacific Heights', 'Russian Hill')],
        start['Sandra'] >= end['Brian'] + travel_times[('Russian Hill', 'Bayview')],
        start['Jason'] >= end['Sandra'] + travel_times[('Bayview', "Fisherman's Wharf")]
    )

    # Add all possible options
    s.add(Or(option1, option2, option3))

    # Maximize the number of friends met
    total_met = Sum([If(meet[name], 1, 0) for name in friends])
    s.maximize(total_met)

    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        for name in sorted(friends.keys()):
            if is_true(m.evaluate(meet[name])):
                start_time = m.evaluate(start[name])
                end_time = m.evaluate(end[name])
                print(f"Meet {name} at {friends[name]['location']} from {float(start_time.numerator_as_long())/float(start_time.denominator_as_long()):.2f} to {float(end_time.numerator_as_long())/float(end_time.denominator_as_long()):.2f}")
        print(f"Total friends met: {m.evaluate(total_met)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()