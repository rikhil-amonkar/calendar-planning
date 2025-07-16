from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define friends and their availability (in minutes since 9:00 AM)
    friends = {
        'Stephanie': {'location': 'Richmond District', 'start': 435, 'end': 750, 'duration': 75},
        'William': {'location': 'Union Square', 'start': 105, 'end': 510, 'duration': 45},
        'Elizabeth': {'location': 'Nob Hill', 'start': 195, 'end': 360, 'duration': 105},
        'Joseph': {'location': 'Fisherman\'s Wharf', 'start': 225, 'end': 300, 'duration': 75},
        'Anthony': {'location': 'Golden Gate Park', 'start': 240, 'end': 690, 'duration': 75},
        'Barbara': {'location': 'Embarcadero', 'start': 495, 'end': 570, 'duration': 75},
        'Carol': {'location': 'Financial District', 'start': 165, 'end': 375, 'duration': 60},
        'Sandra': {'location': 'North Beach', 'start': 60, 'end': 210, 'duration': 15},
        'Kenneth': {'location': 'Presidio', 'start': 615, 'end': 675, 'duration': 45},
    }

    # Travel times in minutes (simplified symmetric version)
    travel_times = {
        ('Marina District', 'Richmond District'): 11,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Fisherman\'s Wharf'): 10,
        ('Marina District', 'Golden Gate Park'): 18,
        ('Marina District', 'Embarcadero'): 14,
        ('Marina District', 'Financial District'): 17,
        ('Marina District', 'North Beach'): 11,
        ('Marina District', 'Presidio'): 10,
        ('Richmond District', 'Union Square'): 21,
        ('Richmond District', 'Nob Hill'): 17,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Richmond District', 'Embarcadero'): 19,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'North Beach'): 17,
        ('Richmond District', 'Presidio'): 7,
        ('Union Square', 'Nob Hill'): 9,
        ('Union Square', 'Fisherman\'s Wharf'): 15,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Embarcadero'): 11,
        ('Union Square', 'Financial District'): 9,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Presidio'): 24,
        ('Nob Hill', 'Fisherman\'s Wharf'): 10,
        ('Nob Hill', 'Golden Gate Park'): 17,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Nob Hill', 'Financial District'): 9,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Fisherman\'s Wharf', 'North Beach'): 6,
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'North Beach'): 23,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Embarcadero', 'Financial District'): 5,
        ('Embarcadero', 'North Beach'): 5,
        ('Embarcadero', 'Presidio'): 20,
        ('Financial District', 'North Beach'): 7,
        ('Financial District', 'Presidio'): 22,
        ('North Beach', 'Presidio'): 17,
    }

    # Make travel times symmetric
    for (loc1, loc2), time in list(travel_times.items()):
        if (loc2, loc1) not in travel_times:
            travel_times[(loc2, loc1)] = time

    # Create variables for each friend's meeting start time (in minutes since 9:00 AM)
    start_vars = {name: Int(f'start_{name}') for name in friends}
    meet_vars = {name: Bool(f'meet_{name}') for name in friends}

    # Current location starts at Marina District at time 0 (9:00 AM)
    current_location = 'Marina District'
    current_time = 0

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        # If we meet this friend, their meeting must be within their window
        s.add(Implies(meet_vars[name], 
                     And(start_vars[name] >= friend['start'],
                         start_vars[name] + friend['duration'] <= friend['end'])))

    # Order constraints - we'll meet friends in some order
    friend_order = [name for name in friends]
    order_vars = {name: Int(f'order_{name}') for name in friends}
    
    # Each friend has a unique order number between 0 and len(friends)-1
    s.add(Distinct([order_vars[name] for name in friends]))
    for name in friends:
        s.add(order_vars[name] >= 0)
        s.add(order_vars[name] < len(friends))

    # Travel time constraints between consecutive meetings
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i != j:
                name1 = friend_order[i]
                name2 = friend_order[j]
                loc1 = friends[name1]['location']
                loc2 = friends[name2]['location']
                travel_time = travel_times.get((loc1, loc2), 60)  # Default high if missing
                
                # If name2 comes right after name1 in order, add travel constraint
                s.add(Implies(And(meet_vars[name1], meet_vars[name2], order_vars[name2] == order_vars[name1] + 1),
                              start_vars[name2] >= start_vars[name1] + friends[name1]['duration'] + travel_time))

    # First meeting must be after arriving at Marina District
    for name in friends:
        loc = friends[name]['location']
        travel_time = travel_times.get(('Marina District', loc), 60)
        s.add(Implies(And(meet_vars[name], order_vars[name] == 0),
                      start_vars[name] >= current_time + travel_time))

    # Maximize the number of friends met
    s.maximize(Sum([If(meet_vars[name], 1, 0) for name in friends]))

    if s.check() == sat:
        m = s.model()
        scheduled = []
        for name in friends:
            if is_true(m[meet_vars[name]]):
                start = m[start_vars[name]].as_long()
                end = start + friends[name]['duration']
                scheduled.append((name, start, end, friends[name]['location']))
        
        # Sort by start time
        scheduled.sort(key=lambda x: x[1])
        
        print("Optimal Schedule:")
        for name, start, end, loc in scheduled:
            start_hr = 9 + start // 60
            start_min = start % 60
            end_hr = 9 + end // 60
            end_min = end % 60
            print(f"Meet {name} at {loc} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}")
        
        print(f"\nTotal friends met: {len(scheduled)}")
    else:
        print("No valid schedule found")

solve_scheduling()