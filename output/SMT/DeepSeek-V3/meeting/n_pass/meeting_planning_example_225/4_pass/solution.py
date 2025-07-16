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
    start = {name: Int(f'start_{name}') for name in friends}
    end = {name: Int(f'end_{name}') for name in friends}

    # Base constraints
    for name in friends:
        f = friends[name]
        s.add(Implies(meet[name], 
                     And(start[name] >= f['start'],
                         end[name] == start[name] + f['duration'],
                         end[name] <= f['end'])))

    # Try to meet all three friends first
    s.push()
    s.add(And([meet[name] for name in friends]))

    # Define possible meeting orders
    # Order 1: Jeffrey -> Sarah -> Brian
    order1 = And(
        start['Jeffrey'] >= travel[('Sunset', 'UnionSquare')],
        end['Jeffrey'] + travel[('UnionSquare', 'NorthBeach')] <= start['Sarah'],
        end['Sarah'] + travel[('NorthBeach', 'AlamoSquare')] <= start['Brian']
    )

    # Order 2: Jeffrey -> Brian -> Sarah
    order2 = And(
        start['Jeffrey'] >= travel[('Sunset', 'UnionSquare')],
        end['Jeffrey'] + travel[('UnionSquare', 'AlamoSquare')] <= start['Brian'],
        end['Brian'] + travel[('AlamoSquare', 'NorthBeach')] <= start['Sarah']
    )

    s.add(Or(order1, order2))

    if s.check() == sat:
        model = s.model()
        print("Optimal schedule meeting all three friends:")
        schedule = []
        for name in friends:
            if is_true(model[meet[name]]):
                s = model[start[name]].as_long()
                e = model[end[name]].as_long()
                schedule.append((name, s, e))
        
        schedule.sort(key=lambda x: x[1])
        for name, s, e in schedule:
            print(f"Meet {name} at {friends[name]['location']} from {9+s//60}:{s%60:02d} to {9+e//60}:{e%60:02d}")
    else:
        print("Cannot meet all three friends. Trying pairs...")
        s.pop()

        # Try meeting pairs
        for pair in [('Jeffrey', 'Sarah'), ('Jeffrey', 'Brian'), ('Sarah', 'Brian')]:
            s.push()
            s.add(And(meet[pair[0]], meet[pair[1]]))
            s.add(And([Not(meet[name]) for name in friends if name not in pair]))

            if 'Jeffrey' in pair:
                other = pair[1]
                s.add(And(
                    start['Jeffrey'] >= travel[('Sunset', 'UnionSquare')],
                    end['Jeffrey'] + travel[('UnionSquare', friends[other]['location'])] <= start[other]
                ))
            else:
                s.add(And(
                    start['Sarah'] >= travel[('Sunset', 'NorthBeach')],
                    end['Sarah'] + travel[('NorthBeach', 'AlamoSquare')] <= start['Brian']
                ))

            if s.check() == sat:
                model = s.model()
                print(f"Schedule meeting {pair[0]} and {pair[1]}:")
                times = []
                for name in pair:
                    if is_true(model[meet[name]]):
                        s = model[start[name]].as_long()
                        e = model[end[name]].as_long()
                        times.append((name, s, e))
                
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
                s.add(start[name] >= travel[('Sunset', friends[name]['location'])])

                if s.check() == sat:
                    model = s.model()
                    s_time = model[start[name]].as_long()
                    e_time = model[end[name]].as_long()
                    print(f"Can only meet {name} at {friends[name]['location']} from {9+s_time//60}:{s_time%60:02d} to {9+e_time//60}:{e_time%60:02d}")
                    break
                s.pop()
            else:
                print("Cannot meet any friends with given constraints.")

solve_scheduling()