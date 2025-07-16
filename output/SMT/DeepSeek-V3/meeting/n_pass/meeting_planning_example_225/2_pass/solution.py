from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Locations
    locations = ['Sunset', 'NorthBeach', 'UnionSquare', 'AlamoSquare']
    
    # Travel times (in minutes) as a dictionary of dictionaries
    travel_times = {
        'Sunset': {'NorthBeach': 29, 'UnionSquare': 30, 'AlamoSquare': 17},
        'NorthBeach': {'Sunset': 27, 'UnionSquare': 7, 'AlamoSquare': 16},
        'UnionSquare': {'Sunset': 26, 'NorthBeach': 10, 'AlamoSquare': 15},
        'AlamoSquare': {'Sunset': 16, 'NorthBeach': 15, 'UnionSquare': 14}
    }

    # Convert all times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(h, m):
        return h * 60 + m - 540  # 9:00 AM is 540 minutes since midnight

    # Friend constraints
    friends = {
        'Sarah': {
            'location': 'NorthBeach',
            'start': time_to_minutes(16, 0),  # 4:00 PM
            'end': time_to_minutes(18, 15),    # 6:15 PM
            'duration': 60                     # 60 minutes
        },
        'Jeffrey': {
            'location': 'UnionSquare',
            'start': time_to_minutes(15, 0),  # 3:00 PM
            'end': time_to_minutes(22, 0),    # 10:00 PM
            'duration': 75                     # 75 minutes
        },
        'Brian': {
            'location': 'AlamoSquare',
            'start': time_to_minutes(16, 0),   # 4:00 PM
            'end': time_to_minutes(17, 30),   # 5:30 PM
            'duration': 75                     # 75 minutes
        }
    }

    # Variables for each friend's meeting start times
    meeting_start = {name: Int(f'start_{name}') for name in friends}
    meeting_attended = {name: Bool(f'attend_{name}') for name in friends}

    # Current location starts at Sunset District at time 0 (9:00 AM)
    current_location = 'Sunset'
    current_time = 0

    # Basic constraints for each friend's meeting
    for name in friends:
        friend = friends[name]
        # If attending, meeting must be within friend's availability
        s.add(Implies(meeting_attended[name], 
                      And(meeting_start[name] >= friend['start'],
                          meeting_start[name] + friend['duration'] <= friend['end'])))

    # We can't be in two places at once, so meetings must be scheduled with travel time
    # We'll create an order of meetings and ensure travel time is accounted for

    # Try to meet all three friends if possible
    all_meetings = And([meeting_attended[name] for name in friends])
    s.push()
    s.add(all_meetings)

    # Possible orders:
    # 1. Jeffrey -> Sarah -> Brian
    order1 = And(
        meeting_start['Jeffrey'] + friends['Jeffrey']['duration'] + 
        travel_times['UnionSquare']['NorthBeach'] <= meeting_start['Sarah'],
        meeting_start['Sarah'] + friends['Sarah']['duration'] + 
        travel_times['NorthBeach']['AlamoSquare'] <= meeting_start['Brian'],
        meeting_start['Jeffrey'] >= travel_times['Sunset']['UnionSquare']
    )

    # 2. Jeffrey -> Brian -> Sarah
    order2 = And(
        meeting_start['Jeffrey'] + friends['Jeffrey']['duration'] + 
        travel_times['UnionSquare']['AlamoSquare'] <= meeting_start['Brian'],
        meeting_start['Brian'] + friends['Brian']['duration'] + 
        travel_times['AlamoSquare']['NorthBeach'] <= meeting_start['Sarah'],
        meeting_start['Jeffrey'] >= travel_times['Sunset']['UnionSquare']
    )

    s.add(Or(order1, order2))

    if s.check() == sat:
        model = s.model()
        print("Optimal schedule (meeting all three friends):")
        for name in sorted(friends.keys(), key=lambda x: model[meeting_start[x]].as_long()):
            if is_true(model[meeting_attended[name]]):
                start = model[meeting_start[name]].as_long()
                end = start + friends[name]['duration']
                print(f"Meet {name} at {friends[name]['location']} from {start//60+9}:{start%60:02d} to {end//60+9}:{end%60:02d}")
    else:
        print("Cannot meet all three friends. Trying combinations of two...")
        s.pop()

        # Try meeting two friends
        for combo in [('Jeffrey', 'Sarah'), ('Jeffrey', 'Brian'), ('Sarah', 'Brian')]:
            s.push()
            s.add(And([meeting_attended[name] for name in combo]))
            s.add(Not(Or([meeting_attended[name] for name in friends if name not in combo]))

            # Jeffrey first
            if 'Jeffrey' in combo:
                other = combo[1]
                s.add(And(
                    meeting_start['Jeffrey'] + friends['Jeffrey']['duration'] + 
                    travel_times['UnionSquare'][friends[other]['location']] <= meeting_start[other],
                    meeting_start['Jeffrey'] >= travel_times['Sunset']['UnionSquare']
                ))
            else:
                # Sarah and Brian
                s.add(And(
                    meeting_start['Sarah'] + friends['Sarah']['duration'] + 
                    travel_times['NorthBeach']['AlamoSquare'] <= meeting_start['Brian'],
                    meeting_start['Sarah'] >= travel_times['Sunset']['NorthBeach']
                ))

            if s.check() == sat:
                model = s.model()
                print(f"Schedule meeting {combo[0]} and {combo[1]}:")
                for name in sorted(combo, key=lambda x: model[meeting_start[x]].as_long()):
                    start = model[meeting_start[name]].as_long()
                    end = start + friends[name]['duration']
                    print(f"Meet {name} at {friends[name]['location']} from {start//60+9}:{start%60:02d} to {end//60+9}:{end%60:02d}")
                break
            s.pop()
        else:
            print("Cannot meet any two friends. Trying individual meetings...")
            for name in friends:
                s.push()
                s.add(meeting_attended[name])
                s.add(Not(Or([meeting_attended[n] for n in friends if n != name])))
                s.add(meeting_start[name] >= travel_times['Sunset'][friends[name]['location']])

                if s.check() == sat:
                    model = s.model()
                    start = model[meeting_start[name]].as_long()
                    end = start + friends[name]['duration']
                    print(f"Can only meet {name} at {friends[name]['location']} from {start//60+9}:{start%60:02d} to {end//60+9}:{end%60:02d}")
                    break
                s.pop()
            else:
                print("Cannot meet any friends with given constraints.")

solve_scheduling()