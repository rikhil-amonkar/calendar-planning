from z3 import *

def solve_scheduling():
    opt = Optimize()

    # Define friends with their constraints
    friends = {
        'Jason': {
            'location': 'Richmond District',
            'available_start': 13 * 60,  # 1:00 PM
            'available_end': 20 * 60 + 45,  # 8:45 PM
            'min_duration': 90
        },
        'Melissa': {
            'location': 'North Beach',
            'available_start': 18 * 60 + 45,  # 6:45 PM
            'available_end': 20 * 60 + 15,  # 8:15 PM
            'min_duration': 45
        },
        'Brian': {
            'location': 'Financial District',
            'available_start': 9 * 60 + 45,  # 9:45 AM
            'available_end': 21 * 60 + 45,  # 9:45 PM
            'min_duration': 15
        },
        'Elizabeth': {
            'location': 'Golden Gate Park',
            'available_start': 8 * 60 + 45,  # 8:45 AM
            'available_end': 21 * 60 + 30,  # 9:30 PM
            'min_duration': 105
        },
        'Laura': {
            'location': 'Union Square',
            'available_start': 14 * 60 + 15,  # 2:15 PM
            'available_end': 19 * 60 + 30,  # 7:30 PM
            'min_duration': 75
        }
    }

    # Travel times between locations (in minutes)
    travel_times = {
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Financial District'): 23,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Union Square'): 22,
        ('Richmond District', 'North Beach'): 17,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Richmond District', 'Union Square'): 21,
        ('North Beach', 'Financial District'): 8,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Union Square'): 7,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Union Square'): 9,
        ('Golden Gate Park', 'Union Square'): 22,
        # Add reverse directions
        **{ (b,a): t for (a,b),t in {
            ('Richmond District', 'Presidio'): 7,
            ('North Beach', 'Presidio'): 17,
            ('Financial District', 'Presidio'): 22,
            ('Golden Gate Park', 'Presidio'): 11,
            ('Union Square', 'Presidio'): 24
        }.items() }
    }

    # Create variables
    meeting_order = {name: Int(f'order_{name}') for name in friends}
    meeting_start = {name: Int(f'start_{name}') for name in friends}
    meeting_end = {name: Int(f'end_{name}') for name in friends}
    meet = {name: Bool(f'meet_{name}') for name in friends}
    current_location = 'Presidio'
    current_time = 0  # 9:00 AM in minutes

    # Each meeting order must be unique if meeting occurs
    for name in friends:
        opt.add(Implies(meet[name], And(meeting_order[name] >= 1, meeting_order[name] <= len(friends))))
        opt.add(Implies(Not(meet[name]), meeting_order[name] == 0))

    opt.add(Distinct([If(meet[name], meeting_order[name], 0) for name in friends]))

    # Base constraints for each friend
    for name, info in friends.items():
        # Convert availability to minutes since 9:00 AM
        start_avail = info['available_start'] - 9 * 60
        end_avail = info['available_end'] - 9 * 60
        min_dur = info['min_duration']

        # If meeting this friend, it must be within their availability and duration
        opt.add(Implies(meet[name], And(
            meeting_start[name] >= start_avail,
            meeting_end[name] <= end_avail,
            meeting_end[name] >= meeting_start[name] + min_dur
        )))

        # If not meeting, set times to 0
        opt.add(Implies(Not(meet[name]), And(
            meeting_start[name] == 0,
            meeting_end[name] == 0,
            meeting_order[name] == 0
        )))

    # Order constraints - ensure travel time is accounted for between meetings
    for name1 in friends:
        for name2 in friends:
            if name1 == name2:
                continue
                
            loc1 = friends[name1]['location']
            loc2 = friends[name2]['location']
            travel_time = travel_times.get((loc1, loc2), 0)
            
            # If both meetings happen and name1 comes before name2
            opt.add(Implies(And(meet[name1], meet[name2], meeting_order[name1] < meeting_order[name2]),
                    meeting_end[name1] + travel_time <= meeting_start[name2]))

    # Initial constraints - first meeting must be after travel from Presidio
    for name in friends:
        loc = friends[name]['location']
        travel_time = travel_times.get(('Presidio', loc), 0)
        opt.add(Implies(And(meet[name], meeting_order[name] == 1),
                       meeting_start[name] >= travel_time))

    # Maximize number of friends met
    opt.maximize(Sum([If(meet[name], 1, 0) for name in friends]))

    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for name in friends:
            if m.evaluate(meet[name]):
                start = m.evaluate(meeting_start[name]).as_long()
                end = m.evaluate(meeting_end[name]).as_long()
                order = m.evaluate(meeting_order[name]).as_long()
                itinerary.append({
                    'order': order,
                    'person': name,
                    'location': friends[name]['location'],
                    'start_time': f"{9 + start // 60}:{start % 60:02d}",
                    'end_time': f"{9 + end // 60}:{end % 60:02d}",
                    'duration': end - start
                })
        
        # Sort itinerary by order
        itinerary.sort(key=lambda x: x['order'])
        
        # Verify all constraints are satisfied
        valid = True
        prev_end = 0
        prev_loc = 'Presidio'
        for item in itinerary:
            travel_time = travel_times.get((prev_loc, item['location']), 0)
            if item['start_time'] < prev_end + travel_time:
                valid = False
                break
            prev_end = item['end_time']
            prev_loc = item['location']
        
        if valid:
            print("Valid Schedule Found:")
            for item in itinerary:
                print(f"{item['order']}. Meet {item['person']} at {item['location']} from {item['start_time']} to {item['end_time']} ({item['duration']} mins)")
            print(f"Total friends met: {len(itinerary)}")
        else:
            print("Found schedule violates constraints. Trying again...")
            # If invalid, add constraints to prevent this solution and try again
            blocking_clause = Or([Not(meet[name]) for name in friends if m.evaluate(meet[name])])
            opt.add(blocking_clause)
            solve_scheduling()  # Recursively try again
    else:
        print("No valid schedule found that satisfies all constraints.")

solve_scheduling()