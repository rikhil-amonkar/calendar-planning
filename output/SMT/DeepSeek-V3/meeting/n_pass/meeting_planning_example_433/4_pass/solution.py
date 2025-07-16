from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define friends and their availability
    friends = {
        'Emily': {'location': 'Richmond District', 'start': 19*60, 'end': 21*60, 'duration': 15},
        'Margaret': {'location': 'Financial District', 'start': 16*60 + 30, 'end': 20*60 + 15, 'duration': 75},
        'Ronald': {'location': 'North Beach', 'start': 18*60 + 30, 'end': 19*60 + 30, 'duration': 45},
        'Deborah': {'location': 'The Castro', 'start': 13*60 + 45, 'end': 21*60 + 15, 'duration': 90},
        'Jeffrey': {'location': 'Golden Gate Park', 'start': 11*60 + 15, 'end': 14*60 + 30, 'duration': 120}
    }

    # Travel times between locations (in minutes)
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

    # Create variables for meeting start times
    start_times = {name: Int(f'start_{name}') for name in friends}
    # Variables to track if we meet each friend
    meet = {name: Bool(f'meet_{name}') for name in friends}

    # Starting at Nob Hill at 9:00 AM (540 minutes)
    current_time = 540

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        # If we meet this friend, their meeting must fit in their window
        s.add(Implies(meet[name],
                     And(start_times[name] >= friend['start'],
                        start_times[name] + friend['duration'] <= friend['end'])))
        
        # Add travel time from Nob Hill to first meeting
        if name in meet:
            loc = friend['location']
            travel = travel_times.get(('Nob Hill', loc), 0)
            s.add(Implies(meet[name], start_times[name] >= current_time + travel))

    # Constraints for travel between meetings
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                loc1 = friends[name1]['location']
                loc2 = friends[name2]['location']
                # Get travel time between locations
                if (loc1, loc2) in travel_times:
                    travel = travel_times[(loc1, loc2)]
                elif (loc2, loc1) in travel_times:
                    travel = travel_times[(loc2, loc1)]
                else:
                    travel = 0
                
                # Ensure proper ordering with travel time
                s.add(Implies(And(meet[name1], meet[name2]),
                             Or(start_times[name2] >= start_times[name1] + friends[name1]['duration'] + travel,
                                start_times[name1] >= start_times[name2] + friends[name2]['duration'] + travel)))

    # Try to maximize the number of friends met
    num_met = Int('num_met')
    s.add(num_met == Sum([If(meet[name], 1, 0) for name in friends]))
    
    # Find the maximum number of friends we can meet
    max_met = 0
    best_model = None
    
    while True:
        s.push()
        s.add(num_met > max_met)
        if s.check() == sat:
            model = s.model()
            current_met = sum(1 for name in friends if is_true(model.eval(meet[name])))
            if current_met > max_met:
                max_met = current_met
                best_model = model
            print(f"Found solution meeting {current_met} friends")
        else:
            s.pop()
            break
        s.pop()

    if best_model is not None:
        print("\nOptimal Schedule:")
        scheduled = [name for name in friends if is_true(best_model.eval(meet[name]))]
        scheduled.sort(key=lambda x: best_model.eval(start_times[x]).as_long())

        for name in scheduled:
            start = best_model.eval(start_times[name]).as_long()
            end = start + friends[name]['duration']
            start_str = f"{start//60:02d}:{start%60:02d}"
            end_str = f"{end//60:02d}:{end%60:02d}"
            print(f"Meet {name} at {friends[name]['location']} from {start_str} to {end_str}")
        print(f"\nTotal friends met: {max_met}")
    else:
        print("No feasible schedule found")

solve_scheduling()