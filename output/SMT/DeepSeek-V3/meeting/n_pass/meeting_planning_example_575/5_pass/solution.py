from z3 import *

def solve_scheduling():
    # Initialize Z3 solver with optimization
    s = Optimize()

    # Define friends and their availability (times in minutes since 9:00 AM)
    friends = {
        'Rebecca': {'location': 'Presidio', 'start': 555, 'end': 645, 'duration': 60},
        'Linda': {'location': 'Sunset District', 'start': 390, 'end': 465, 'duration': 30},
        'Elizabeth': {'location': 'Haight-Ashbury', 'start': 495, 'end': 570, 'duration': 105},
        'William': {'location': 'Mission District', 'start': 255, 'end': 570, 'duration': 30},
        'Robert': {'location': 'Golden Gate Park', 'start': 315, 'end': 750, 'duration': 45},
        'Mark': {'location': 'Russian Hill', 'start': 60, 'end': 735, 'duration': 75}
    }

    # Travel times between locations (in minutes)
    travel_times = {
        ('The Castro', 'Presidio'): 20,
        ('The Castro', 'Sunset District'): 17,
        ('The Castro', 'Haight-Ashbury'): 6,
        ('The Castro', 'Mission District'): 7,
        ('The Castro', 'Golden Gate Park'): 11,
        ('The Castro', 'Russian Hill'): 18,
        ('Presidio', 'The Castro'): 21,
        ('Presidio', 'Sunset District'): 15,
        ('Presidio', 'Haight-Ashbury'): 15,
        ('Presidio', 'Mission District'): 26,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Russian Hill'): 14,
        ('Sunset District', 'The Castro'): 17,
        ('Sunset District', 'Presidio'): 16,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'Mission District'): 24,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Russian Hill'): 24,
        ('Haight-Ashbury', 'The Castro'): 6,
        ('Haight-Ashbury', 'Presidio'): 15,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Mission District', 'The Castro'): 7,
        ('Mission District', 'Presidio'): 25,
        ('Mission District', 'Sunset District'): 24,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'Russian Hill'): 15,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', 'Golden Gate Park'): 21
    }

    # Create Z3 variables (all times in minutes since 9:00 AM)
    start_vars = {name: Int(f'start_{name}') for name in friends}
    end_vars = {name: Int(f'end_{name}') for name in friends}
    meet_vars = {name: Bool(f'meet_{name}') for name in friends}

    # Starting point (9:00 AM = 0 minutes)
    current_time = 0
    current_location = 'The Castro'

    # Add constraints for each friend
    for name in friends:
        friend = friends[name]
        # If meeting, must be within their availability
        s.add(Implies(meet_vars[name], start_vars[name] >= friend['start']))
        s.add(Implies(meet_vars[name], end_vars[name] <= friend['end']))
        s.add(Implies(meet_vars[name], end_vars[name] == start_vars[name] + friend['duration']))
        # First meeting must account for travel from starting location
        s.add(Implies(meet_vars[name], start_vars[name] >= current_time + travel_times[(current_location, friend['location'])]))

    # No overlapping meetings considering travel time
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                loc1 = friends[name1]['location']
                loc2 = friends[name2]['location']
                travel = travel_times[(loc1, loc2)]
                s.add(Implies(And(meet_vars[name1], meet_vars[name2]),
                              Or(end_vars[name1] + travel <= start_vars[name2],
                                 end_vars[name2] + travel_times[(loc2, loc1)] <= start_vars[name1])))

    # Maximize number of friends met
    s.maximize(Sum([If(meet_vars[name], 1, 0) for name in friends]))

    # Solve and print results
    if s.check() == sat:
        model = s.model()
        scheduled = []
        for name in friends:
            if is_true(model.evaluate(meet_vars[name])):
                start = model.evaluate(start_vars[name]).as_long()
                end = model.evaluate(end_vars[name]).as_long()
                scheduled.append((name, start, end))
        
        # Sort by start time
        scheduled.sort(key=lambda x: x[1])
        
        print("Optimal Schedule:")
        for name, start, end in scheduled:
            # Convert minutes to HH:MM format
            start_time = f"{9 + start // 60}:{start % 60:02d}"
            end_time = f"{9 + end // 60}:{end % 60:02d}"
            print(f"Meet {name} at {friends[name]['location']} from {start_time} to {end_time}")
        
        print(f"\nTotal friends met: {len(scheduled)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()