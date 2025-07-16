from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define friends and their availability
    friends = [
        {'name': 'Emily', 'location': 'Richmond District', 'start': 19*60, 'end': 21*60, 'duration': 15},
        {'name': 'Margaret', 'location': 'Financial District', 'start': 16*60+30, 'end': 20*60+15, 'duration': 75},
        {'name': 'Ronald', 'location': 'North Beach', 'start': 18*60+30, 'end': 19*60+30, 'duration': 45},
        {'name': 'Deborah', 'location': 'The Castro', 'start': 13*60+45, 'end': 21*60+15, 'duration': 90},
        {'name': 'Jeffrey', 'location': 'Golden Gate Park', 'start': 11*60+15, 'end': 14*60+30, 'duration': 120}
    ]

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
    start_vars = {f['name']: Int(f'start_{f["name"]}') for f in friends}
    # Variables to track if we meet each friend
    meet_vars = {f['name']: Bool(f'meet_{f["name"]}') for f in friends}

    # Starting at Nob Hill at 9:00 AM (540 minutes)
    current_time = 540

    # Constraints for each friend
    for f in friends:
        name = f['name']
        # If we meet this friend, their meeting must fit in their window
        s.add(Implies(meet_vars[name],
                     And(start_vars[name] >= f['start'],
                        start_vars[name] + f['duration'] <= f['end'])))
        
        # Add travel time from Nob Hill to first meeting
        travel = travel_times.get(('Nob Hill', f['location']), 0)
        s.add(Implies(meet_vars[name], start_vars[name] >= current_time + travel))

    # Constraints for travel between meetings
    for i in range(len(friends)):
        for j in range(i+1, len(friends)):
            f1 = friends[i]
            f2 = friends[j]
            
            # Get travel time between locations
            if (f1['location'], f2['location']) in travel_times:
                travel = travel_times[(f1['location'], f2['location'])]
            elif (f2['location'], f1['location']) in travel_times:
                travel = travel_times[(f2['location'], f1['location'])]
            else:
                travel = 0
            
            # Ensure proper ordering with travel time
            s.add(Implies(And(meet_vars[f1['name']], meet_vars[f2['name']]),
                         Or(start_vars[f2['name']] >= start_vars[f1['name']] + f1['duration'] + travel,
                            start_vars[f1['name']] >= start_vars[f2['name']] + f2['duration'] + travel)))

    # Objective: maximize number of friends met
    num_met = Int('num_met')
    s.add(num_met == Sum([If(meet_vars[f['name']], 1, 0) for f in friends]))
    
    # Find solution that maximizes num_met
    max_met = 0
    best_model = None
    
    while True:
        s.push()
        s.add(num_met > max_met)
        if s.check() == sat:
            model = s.model()
            current_met = sum(1 for f in friends if is_true(model.eval(meet_vars[f['name']])))
            if current_met > max_met:
                max_met = current_met
                best_model = model
            print(f"Found solution meeting {current_met} friends")
        else:
            s.pop()
            break
        s.pop()

    if best_model:
        print("\nOptimal Schedule:")
        scheduled = [f for f in friends if is_true(best_model.eval(meet_vars[f['name']]))]
        scheduled.sort(key=lambda f: best_model.eval(start_vars[f['name']]).as_long())

        for f in scheduled:
            start = best_model.eval(start_vars[f['name']]).as_long()
            end = start + f['duration']
            start_str = f"{start//60:02d}:{start%60:02d}"
            end_str = f"{end//60:02d}:{end%60:02d}"
            print(f"Meet {f['name']} at {f['location']} from {start_str} to {end_str}")
        print(f"\nTotal friends met: {max_met}")
    else:
        print("No feasible schedule found")

solve_scheduling()