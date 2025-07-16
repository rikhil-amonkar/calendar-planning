from z3 import *

def solve_scheduling():
    s = Solver()

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

    # Constraints for each friend
    for name in friends:
        data = friends[name]
        s.add(Implies(meet[name], start[name] >= data['start']))
        s.add(Implies(meet[name], end[name] <= data['end']))
        s.add(Implies(meet[name], end[name] == start[name] + data['min_duration']))

    # Meeting Richard first if possible
    s.add(Implies(meet['Richard'], start['Richard'] >= current_time + travel_times[(current_location, 'Pacific Heights')]))

    # After Richard, next possible meetings
    # We'll try to meet Stephanie after Richard
    s.add(Implies(And(meet['Richard'], meet['Stephanie']), 
                  start['Stephanie'] >= end['Richard'] + travel_times[('Pacific Heights', 'Mission District')]))

    # After Stephanie, meet Brian
    s.add(Implies(And(meet['Stephanie'], meet['Brian']), 
                  start['Brian'] >= end['Stephanie'] + travel_times[('Mission District', 'Russian Hill')]))

    # After Brian, meet Sandra
    s.add(Implies(And(meet['Brian'], meet['Sandra']), 
                  start['Sandra'] >= end['Brian'] + travel_times[('Russian Hill', 'Bayview')]))

    # After Sandra, meet Jason
    s.add(Implies(And(meet['Sandra'], meet['Jason']), 
                  start['Jason'] >= end['Sandra'] + travel_times[('Bayview', "Fisherman's Wharf")]))

    # Alternative paths if some friends are not met
    # For example, if Richard is not met, start with Stephanie
    s.add(Implies(And(Not(meet['Richard']), meet['Stephanie']), 
                  start['Stephanie'] >= current_time + travel_times[(current_location, 'Mission District')]))

    # After Stephanie, meet Brian
    s.add(Implies(And(Not(meet['Richard']), meet['Stephanie'], meet['Brian']), 
                  start['Brian'] >= end['Stephanie'] + travel_times[('Mission District', 'Russian Hill')]))

    # Similarly, other possible sequences can be added.

    # Maximize the number of friends met
    s.maximize(Sum([If(meet[name], 1, 0) for name in friends]))

    if s.check() == sat:
        m = s.model()
        total = 0
        print("SOLUTION:")
        for name in friends:
            if m.evaluate(meet[name]):
                total += 1
                start_time = m.evaluate(start[name])
                end_time = m.evaluate(end[name])
                print(f"Meet {name} at {friends[name]['location']} from {start_time} to {end_time}")
        print(f"Total friends met: {total}")
    else:
        print("No feasible schedule found.")

solve_scheduling()