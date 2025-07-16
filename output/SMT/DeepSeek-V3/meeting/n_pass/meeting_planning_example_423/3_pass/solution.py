from z3 import *

def solve_scheduling():
    opt = Optimize()

    # Define locations and friends
    friends = {
        'Jason': {'location': 'Richmond District', 'start': 13*60, 'end': 20*60 + 45, 'min_duration': 90},
        'Melissa': {'location': 'North Beach', 'start': 18*60 + 45, 'end': 20*60 + 15, 'min_duration': 45},
        'Brian': {'location': 'Financial District', 'start': 9*60 + 45, 'end': 21*60 + 45, 'min_duration': 15},
        'Elizabeth': {'location': 'Golden Gate Park', 'start': 8*60 + 45, 'end': 21*60 + 30, 'min_duration': 105},
        'Laura': {'location': 'Union Square', 'start': 14*60 + 15, 'end': 19*60 + 30, 'min_duration': 75}
    }

    # Travel times (in minutes)
    travel_times = {
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Financial District'): 23,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Union Square'): 22,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'North Beach'): 17,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Richmond District', 'Union Square'): 21,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Richmond District'): 18,
        ('North Beach', 'Financial District'): 8,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Union Square'): 7,
        ('Financial District', 'Presidio'): 22,
        ('Financial District', 'Richmond District'): 21,
        ('Financial District', 'North Beach'): 7,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Union Square'): 9,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'Richmond District'): 20,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Financial District'): 9,
        ('Union Square', 'Golden Gate Park'): 22
    }

    # Variables
    meeting_start = {name: Int(f'start_{name}') for name in friends}
    meeting_end = {name: Int(f'end_{name}') for name in friends}
    meet = {name: Bool(f'meet_{name}') for name in friends}
    current_location = 'Presidio'
    current_time = 0  # 9:00 AM

    # Constraints for each friend
    for name in friends:
        info = friends[name]
        loc = info['location']
        start_avail = info['start'] - 9*60  # Convert to minutes since 9:00 AM
        end_avail = info['end'] - 9*60
        min_dur = info['min_duration']

        opt.add(Implies(meet[name], And(
            meeting_start[name] >= start_avail,
            meeting_end[name] <= end_avail,
            meeting_end[name] >= meeting_start[name] + min_dur
        )))
        opt.add(Implies(Not(meet[name]), And(
            meeting_start[name] == 0,
            meeting_end[name] == 0
        )))

    # Order constraints and travel times
    friend_names = list(friends.keys())
    for i in range(len(friend_names)):
        for j in range(i+1, len(friend_names)):
            name1 = friend_names[i]
            name2 = friend_names[j]
            loc1 = friends[name1]['location']
            loc2 = friends[name2]['location']
            travel_time = travel_times.get((loc1, loc2), 0)

            # Ensure no overlap when both meetings are scheduled
            opt.add(Implies(And(meet[name1], meet[name2]),
                Or(
                    meeting_end[name1] + travel_time <= meeting_start[name2],
                    meeting_end[name2] + travel_time <= meeting_start[name1]
                )
            ))

    # Maximize number of friends met
    opt.maximize(Sum([If(meet[name], 1, 0) for name in friends]))

    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for name in friends:
            if m.evaluate(meet[name]):
                start = m.evaluate(meeting_start[name]).as_long()
                end = m.evaluate(meeting_end[name]).as_long()
                itinerary.append({
                    'action': 'meet',
                    'person': name,
                    'start_time': f"{9 + start // 60}:{start % 60:02d}",
                    'end_time': f"{9 + end // 60}:{end % 60:02d}",
                    'location': friends[name]['location']
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        print("Valid Schedule:")
        for item in itinerary:
            print(f"Meet {item['person']} at {item['location']} from {item['start_time']} to {item['end_time']}")
        print(f"Total friends met: {len(itinerary)}")
    else:
        print("No valid schedule found that satisfies all constraints.")

solve_scheduling()