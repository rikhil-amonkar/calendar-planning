from z3 import *

def solve_scheduling():
    s = Solver()

    # Define locations and friends data
    friends = {
        'Emily': {'location': 'Richmond District', 'start': 19*60, 'end': 21*60, 'min_duration': 15},
        'Margaret': {'location': 'Financial District', 'start': 16*60 + 30, 'end': 20*60 + 15, 'min_duration': 75},
        'Ronald': {'location': 'North Beach', 'start': 18*60 + 30, 'end': 19*60 + 30, 'min_duration': 45},
        'Deborah': {'location': 'The Castro', 'start': 13*60 + 45, 'end': 21*60 + 15, 'min_duration': 90},
        'Jeffrey': {'location': 'Golden Gate Park', 'start': 11*60 + 15, 'end': 14*60 + 30, 'min_duration': 120}
    }

    # Travel times matrix (in minutes)
    travel_times = {
        ('Nob Hill', 'Richmond District'): 14,
        ('Nob Hill', 'Financial District'): 9,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'Golden Gate Park'): 17,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'North Beach'): 17,
        ('Richmond District', 'The Castro'): 16,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Financial District', 'North Beach'): 7,
        ('Financial District', 'The Castro'): 23,
        ('Financial District', 'Golden Gate Park'): 23,
        ('North Beach', 'The Castro'): 22,
        ('North Beach', 'Golden Gate Park'): 22,
        ('The Castro', 'Golden Gate Park'): 11,
    }

    # Create variables for meeting times
    meeting_start = {name: Int(f'start_{name}') for name in friends}
    meeting_end = {name: Int(f'end_{name}') for name in friends}

    # Create variables to track if we meet each friend
    meet_friend = {name: Bool(f'meet_{name}') for name in friends}

    # Basic constraints for each friend
    for name in friends:
        data = friends[name]
        s.add(Implies(meet_friend[name], 
                     And(meeting_start[name] >= data['start'],
                         meeting_end[name] <= data['end'],
                         meeting_end[name] == meeting_start[name] + data['min_duration'])))

    # Starting at Nob Hill at 9:00 AM (540 minutes)
    current_time = 540
    first_meeting = None

    # Determine meeting order
    friend_names = list(friends.keys())
    for i in range(len(friend_names)):
        for j in range(i+1, len(friend_names)):
            name1 = friend_names[i]
            name2 = friend_names[j]
            loc1 = friends[name1]['location']
            loc2 = friends[name2]['location']
            
            # Get travel time between locations
            if (loc1, loc2) in travel_times:
                travel = travel_times[(loc1, loc2)]
            elif (loc2, loc1) in travel_times:
                travel = travel_times[(loc2, loc1)]
            else:
                travel = 0  # Shouldn't happen with complete travel matrix
            
            # Ensure proper ordering with travel time
            s.add(Implies(And(meet_friend[name1], meet_friend[name2]),
                         Or(meeting_start[name2] >= meeting_end[name1] + travel,
                            meeting_start[name1] >= meeting_end[name2] + travel)))

    # Starting location constraints
    for name in friends:
        loc = friends[name]['location']
        travel = travel_times.get(('Nob Hill', loc), 0)
        s.add(Implies(meet_friend[name], meeting_start[name] >= current_time + travel))

    # Try to meet as many friends as possible
    num_met = Sum([If(meet_friend[name], 1, 0) for name in friends])
    max_met = 0
    model = None

    # Find the maximum number of friends we can meet
    while True:
        s.push()
        s.add(num_met > max_met)
        if s.check() == sat:
            model = s.model()
            max_met = sum(1 for name in friends if is_true(model.eval(meet_friend[name])))
            print(f"Found solution meeting {max_met} friends")
        else:
            s.pop()
            break
        s.pop()

    if model is not None:
        print("\nOptimal Schedule:")
        scheduled = [name for name in friends if is_true(model.eval(meet_friend[name]))]
        scheduled.sort(key=lambda x: model.eval(meeting_start[x]).as_long())

        for name in scheduled:
            start = model.eval(meeting_start[name]).as_long()
            end = model.eval(meeting_end[name]).as_long()
            start_str = f"{start//60:02d}:{start%60:02d}"
            end_str = f"{end//60:02d}:{end%60:02d}"
            print(f"Meet {name} at {friends[name]['location']} from {start_str} to {end_str}")
        print(f"\nTotal friends met: {max_met}")
    else:
        print("No feasible schedule found")

solve_scheduling()