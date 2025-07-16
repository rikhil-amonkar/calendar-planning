from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Travel times between locations (in minutes)
    travel_times = {
        ('Sunset', 'NorthBeach'): 29,
        ('Sunset', 'UnionSquare'): 30,
        ('Sunset', 'AlamoSquare'): 17,
        ('NorthBeach', 'Sunset'): 27,
        ('NorthBeach', 'UnionSquare'): 7,
        ('NorthBeach', 'AlamoSquare'): 16,
        ('UnionSquare', 'Sunset'): 26,
        ('UnionSquare', 'NorthBeach'): 10,
        ('UnionSquare', 'AlamoSquare'): 15,
        ('AlamoSquare', 'Sunset'): 16,
        ('AlamoSquare', 'NorthBeach'): 15,
        ('AlamoSquare', 'UnionSquare'): 14
    }

    # Friend availability (converted to minutes since 9:00 AM)
    friends = {
        'Sarah': {
            'location': 'NorthBeach',
            'start': 16*60 - 9*60,    # 4:00 PM (960 mins) - 9:00 AM (540 mins) = 420
            'end': 18*60 + 15 - 9*60, # 6:15 PM (1095 mins) - 540 = 555
            'duration': 60
        },
        'Jeffrey': {
            'location': 'UnionSquare',
            'start': 15*60 - 9*60,    # 3:00 PM (900 mins) - 540 = 360
            'end': 22*60 - 9*60,      # 10:00 PM (1320 mins) - 540 = 780
            'duration': 75
        },
        'Brian': {
            'location': 'AlamoSquare',
            'start': 16*60 - 9*60,     # 4:00 PM (960 mins) - 540 = 420
            'end': 17*60 + 30 - 9*60,  # 5:30 PM (1050 mins) - 540 = 510
            'duration': 75
        }
    }

    # Create variables for meeting start times
    meeting_start = {name: Int(f'start_{name}') for name in friends}
    meeting_end = {name: Int(f'end_{name}') for name in friends}
    meet_friend = {name: Bool(f'meet_{name}') for name in friends}

    # Current location starts at Sunset District at time 0 (9:00 AM)
    current_location = 'Sunset'
    current_time = 0

    # Basic constraints for each friend
    for name in friends:
        friend = friends[name]
        # If meeting, must be within their availability
        s.add(Implies(meet_friend[name], 
                     And(meeting_start[name] >= friend['start'],
                         meeting_end[name] == meeting_start[name] + friend['duration'],
                         meeting_end[name] <= friend['end'])))

    # Try to meet all three friends first
    all_meetings = And([meet_friend[name] for name in friends])
    s.push()
    s.add(all_meetings)

    # Define possible meeting orders with travel times
    # Order 1: Jeffrey -> Sarah -> Brian
    order1 = And(
        meeting_start['Jeffrey'] >= travel_times[('Sunset', 'UnionSquare')],
        meeting_end['Jeffrey'] + travel_times[('UnionSquare', 'NorthBeach')] <= meeting_start['Sarah'],
        meeting_end['Sarah'] + travel_times[('NorthBeach', 'AlamoSquare')] <= meeting_start['Brian']
    )

    # Order 2: Jeffrey -> Brian -> Sarah
    order2 = And(
        meeting_start['Jeffrey'] >= travel_times[('Sunset', 'UnionSquare')],
        meeting_end['Jeffrey'] + travel_times[('UnionSquare', 'AlamoSquare')] <= meeting_start['Brian'],
        meeting_end['Brian'] + travel_times[('AlamoSquare', 'NorthBeach')] <= meeting_start['Sarah']
    )

    s.add(Or(order1, order2))

    if s.check() == sat:
        model = s.model()
        print("Optimal schedule meeting all three friends:")
        schedule = []
        for name in friends:
            if is_true(model[meet_friend[name]]):
                start = model[meeting_start[name]].as_long()
                end = model[meeting_end[name]].as_long()
                schedule.append((name, start, end))
        
        # Sort by start time
        schedule.sort(key=lambda x: x[1])
        for name, start, end in schedule:
            start_h = (start + 540) // 60
            start_m = (start + 540) % 60
            end_h = (end + 540) // 60
            end_m = (end + 540) % 60
            print(f"Meet {name} at {friends[name]['location']} from {start_h}:{start_m:02d} to {end_h}:{end_m:02d}")
    else:
        print("Cannot meet all three friends. Trying combinations of two...")
        s.pop()

        # Try meeting pairs of friends
        for combo in [['Jeffrey', 'Sarah'], ['Jeffrey', 'Brian'], ['Sarah', 'Brian']]:
            s.push()
            s.add(And([meet_friend[name] for name in combo]))
            s.add(And([Not(meet_friend[name]) for name in friends if name not in combo]))

            # Jeffrey first if in combo
            if 'Jeffrey' in combo:
                other = combo[1]
                s.add(And(
                    meeting_start['Jeffrey'] >= travel_times[('Sunset', 'UnionSquare')],
                    meeting_end['Jeffrey'] + travel_times[('UnionSquare', friends[other]['location'])] <= meeting_start[other]
                ))
            else:
                # Sarah and Brian
                s.add(And(
                    meeting_start['Sarah'] >= travel_times[('Sunset', 'NorthBeach')],
                    meeting_end['Sarah'] + travel_times[('NorthBeach', 'AlamoSquare')] <= meeting_start['Brian']
                ))

            if s.check() == sat:
                model = s.model()
                print(f"Schedule meeting {combo[0]} and {combo[1]}:")
                schedule = []
                for name in combo:
                    if is_true(model[meet_friend[name]]):
                        start = model[meeting_start[name]].as_long()
                        end = model[meeting_end[name]].as_long()
                        schedule.append((name, start, end))
                
                schedule.sort(key=lambda x: x[1])
                for name, start, end in schedule:
                    start_h = (start + 540) // 60
                    start_m = (start + 540) % 60
                    end_h = (end + 540) // 60
                    end_m = (end + 540) % 60
                    print(f"Meet {name} at {friends[name]['location']} from {start_h}:{start_m:02d} to {end_h}:{end_m:02d}")
                break
            s.pop()
        else:
            print("Cannot meet any two friends. Trying individual meetings...")
            for name in friends:
                s.push()
                s.add(meet_friend[name])
                s.add(And([Not(meet_friend[n]) for n in friends if n != name]))
                s.add(meeting_start[name] >= travel_times[('Sunset', friends[name]['location'])])

                if s.check() == sat:
                    model = s.model()
                    start = model[meeting_start[name]].as_long()
                    end = model[meeting_end[name]].as_long()
                    start_h = (start + 540) // 60
                    start_m = (start + 540) % 60
                    end_h = (end + 540) // 60
                    end_m = (end + 540) % 60
                    print(f"Can only meet {name} at {friends[name]['location']} from {start_h}:{start_m:02d} to {end_h}:{end_m:02d}")
                    break
                s.pop()
            else:
                print("Cannot meet any friends with given constraints.")

solve_scheduling()