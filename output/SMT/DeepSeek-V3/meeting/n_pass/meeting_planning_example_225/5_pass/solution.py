from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Travel times between locations (in minutes)
    travel = {
        ('Sunset', 'NorthBeach'): 29,
        ('Sunset', 'UnionSquare'): 30,
        ('Sunset', 'AlamoSquare'): 17,
        ('NorthBeach', 'UnionSquare'): 7,
        ('NorthBeach', 'AlamoSquare'): 16,
        ('UnionSquare', 'NorthBeach'): 10,
        ('UnionSquare', 'AlamoSquare'): 15,
        ('AlamoSquare', 'NorthBeach'): 15,
        ('AlamoSquare', 'UnionSquare'): 14
    }

    # Friend availability (minutes since 9:00 AM)
    friends = {
        'Sarah': {
            'location': 'NorthBeach',
            'start': 420,  # 4:00 PM (16*60 - 9*60)
            'end': 555,    # 6:15 PM (18*60+15 - 9*60)
            'duration': 60
        },
        'Jeffrey': {
            'location': 'UnionSquare',
            'start': 360,  # 3:00 PM (15*60 - 9*60)
            'end': 780,    # 10:00 PM (22*60 - 9*60)
            'duration': 75
        },
        'Brian': {
            'location': 'AlamoSquare',
            'start': 420,  # 4:00 PM (16*60 - 9*60)
            'end': 510,    # 5:30 PM (17*60+30 - 9*60)
            'duration': 75
        }
    }

    # Decision variables
    meet = {name: Bool(f'meet_{name}') for name in friends}
    start_times = {name: Int(f'start_{name}') for name in friends}

    # Base constraints for each friend
    for name in friends:
        f = friends[name]
        s.add(Implies(meet[name], 
                     And(start_times[name] >= f['start'],
                         start_times[name] + f['duration'] <= f['end'])))

    # Try to meet all three friends first
    s.push()
    s.add(And([meet[name] for name in friends]))

    # Define possible meeting orders with travel times
    # Order 1: Jeffrey -> Sarah -> Brian
    order1 = And(
        start_times['Jeffrey'] >= travel[('Sunset', 'UnionSquare')],
        start_times['Jeffrey'] + friends['Jeffrey']['duration'] + travel[('UnionSquare', 'NorthBeach')] <= start_times['Sarah'],
        start_times['Sarah'] + friends['Sarah']['duration'] + travel[('NorthBeach', 'AlamoSquare')] <= start_times['Brian']
    )

    # Order 2: Jeffrey -> Brian -> Sarah
    order2 = And(
        start_times['Jeffrey'] >= travel[('Sunset', 'UnionSquare')],
        start_times['Jeffrey'] + friends['Jeffrey']['duration'] + travel[('UnionSquare', 'AlamoSquare')] <= start_times['Brian'],
        start_times['Brian'] + friends['Brian']['duration'] + travel[('AlamoSquare', 'NorthBeach')] <= start_times['Sarah']
    )

    s.add(Or(order1, order2))

    if s.check() == sat:
        model = s.model()
        print("Optimal schedule meeting all three friends:")
        schedule = []
        for name in friends:
            if is_true(model[meet[name]]):
                s_time = model[start_times[name]].as_long()
                e_time = s_time + friends[name]['duration']
                schedule.append((name, s_time, e_time))
        
        # Sort by start time
        schedule.sort(key=lambda x: x[1])
        for name, s, e in schedule:
            print(f"Meet {name} at {friends[name]['location']} from {9+s//60}:{s%60:02d} to {9+e//60}:{e%60:02d}")
    else:
        print("Cannot meet all three friends. Trying pairs...")
        s.pop()

        # Try meeting pairs of friends
        for pair in [('Jeffrey', 'Sarah'), ('Jeffrey', 'Brian'), ('Sarah', 'Brian')]:
            s.push()
            s.add(And(meet[pair[0]], meet[pair[1]]))
            s.add(And([Not(meet[name]) for name in friends if name not in pair]))

            if 'Jeffrey' in pair:
                other = pair[1]
                s.add(And(
                    start_times['Jeffrey'] >= travel[('Sunset', 'UnionSquare')],
                    start_times['Jeffrey'] + friends['Jeffrey']['duration'] + travel[('UnionSquare', friends[other]['location'])] <= start_times[other]
                ))
            else:
                s.add(And(
                    start_times['Sarah'] >= travel[('Sunset', 'NorthBeach')],
                    start_times['Sarah'] + friends['Sarah']['duration'] + travel[('NorthBeach', 'AlamoSquare')] <= start_times['Brian']
                ))

            if s.check() == sat:
                model = s.model()
                print(f"Schedule meeting {pair[0]} and {pair[1]}:")
                times = []
                for name in pair:
                    if is_true(model[meet[name]]):
                        s_time = model[start_times[name]].as_long()
                        e_time = s_time + friends[name]['duration']
                        times.append((name, s_time, e_time))
                
                times.sort(key=lambda x: x[1])
                for name, s, e in times:
                    print(f"Meet {name} at {friends[name]['location']} from {9+s//60}:{s%60:02d} to {9+e//60}:{e%60:02d}")
                break
            s.pop()
        else:
            print("Cannot meet any two friends. Trying individuals...")
            for name in friends:
                s.push()
                s.add(meet[name])
                s.add(And([Not(meet[n]) for n in friends if n != name]))
                s.add(start_times[name] >= travel[('Sunset', friends[name]['location'])])

                if s.check() == sat:
                    model = s.model()
                    s_time = model[start_times[name]].as_long()
                    e_time = s_time + friends[name]['duration']
                    print(f"Can only meet {name} at {friends[name]['location']} from {9+s_time//60}:{s_time%60:02d} to {9+e_time//60}:{e_time%60:02d}")
                    break
                s.pop()
            else:
                print("Cannot meet any friends with given constraints.")

solve_scheduling()