from z3 import *

def solve_scheduling():
    # Initialize Z3 solver with optimization
    s = Optimize()

    # Define friends and their availability (times in hours since midnight)
    friends = {
        'Rebecca': {'location': 'Presidio', 'start': 18.25, 'end': 20.75, 'duration': 1.0},
        'Linda': {'location': 'Sunset District', 'start': 15.5, 'end': 19.75, 'duration': 0.5},
        'Elizabeth': {'location': 'Haight-Ashbury', 'start': 17.25, 'end': 19.5, 'duration': 1.75},
        'William': {'location': 'Mission District', 'start': 13.25, 'end': 19.5, 'duration': 0.5},
        'Robert': {'location': 'Golden Gate Park', 'start': 14.25, 'end': 21.5, 'duration': 0.75},
        'Mark': {'location': 'Russian Hill', 'start': 10.0, 'end': 21.25, 'duration': 1.25}
    }

    # Travel times between locations (in hours)
    travel_times = {
        ('The Castro', 'Presidio'): 20/60,
        ('The Castro', 'Sunset District'): 17/60,
        ('The Castro', 'Haight-Ashbury'): 6/60,
        ('The Castro', 'Mission District'): 7/60,
        ('The Castro', 'Golden Gate Park'): 11/60,
        ('The Castro', 'Russian Hill'): 18/60,
        ('Presidio', 'The Castro'): 21/60,
        ('Presidio', 'Sunset District'): 15/60,
        ('Presidio', 'Haight-Ashbury'): 15/60,
        ('Presidio', 'Mission District'): 26/60,
        ('Presidio', 'Golden Gate Park'): 12/60,
        ('Presidio', 'Russian Hill'): 14/60,
        ('Sunset District', 'The Castro'): 17/60,
        ('Sunset District', 'Presidio'): 16/60,
        ('Sunset District', 'Haight-Ashbury'): 15/60,
        ('Sunset District', 'Mission District'): 24/60,
        ('Sunset District', 'Golden Gate Park'): 11/60,
        ('Sunset District', 'Russian Hill'): 24/60,
        ('Haight-Ashbury', 'The Castro'): 6/60,
        ('Haight-Ashbury', 'Presidio'): 15/60,
        ('Haight-Ashbury', 'Sunset District'): 15/60,
        ('Haight-Ashbury', 'Mission District'): 11/60,
        ('Haight-Ashbury', 'Golden Gate Park'): 7/60,
        ('Haight-Ashbury', 'Russian Hill'): 17/60,
        ('Mission District', 'The Castro'): 7/60,
        ('Mission District', 'Presidio'): 25/60,
        ('Mission District', 'Sunset District'): 24/60,
        ('Mission District', 'Haight-Ashbury'): 12/60,
        ('Mission District', 'Golden Gate Park'): 17/60,
        ('Mission District', 'Russian Hill'): 15/60,
        ('Golden Gate Park', 'The Castro'): 13/60,
        ('Golden Gate Park', 'Presidio'): 11/60,
        ('Golden Gate Park', 'Sunset District'): 10/60,
        ('Golden Gate Park', 'Haight-Ashbury'): 7/60,
        ('Golden Gate Park', 'Mission District'): 17/60,
        ('Golden Gate Park', 'Russian Hill'): 19/60,
        ('Russian Hill', 'The Castro'): 21/60,
        ('Russian Hill', 'Presidio'): 14/60,
        ('Russian Hill', 'Sunset District'): 23/60,
        ('Russian Hill', 'Haight-Ashbury'): 17/60,
        ('Russian Hill', 'Mission District'): 16/60,
        ('Russian Hill', 'Golden Gate Park'): 21/60
    }

    # Create Z3 variables
    start_vars = {name: Real(f'start_{name}') for name in friends}
    end_vars = {name: Real(f'end_{name}') for name in friends}
    meet_vars = {name: Bool(f'meet_{name}') for name in friends}

    # Starting point
    current_time = 9.0  # 9:00 AM
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
            if model.evaluate(meet_vars[name]):
                start = float(model.evaluate(start_vars[name]).as_fraction()
                end = float(model.evaluate(end_vars[name]).as_fraction()
                scheduled.append((name, start, end))
        
        # Sort by start time
        scheduled.sort(key=lambda x: x[1])
        
        print("Optimal Schedule:")
        for name, start, end in scheduled:
            # Convert decimal hours to HH:MM format
            start_h = int(start)
            start_m = int(round((start - start_h) * 60))
            end_h = int(end)
            end_m = int(round((end - end_h) * 60))
            print(f"Meet {name} at {friends[name]['location']} from {start_h}:{start_m:02d} to {end_h}:{end_m:02d}")
        
        print(f"\nTotal friends met: {len(scheduled)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()