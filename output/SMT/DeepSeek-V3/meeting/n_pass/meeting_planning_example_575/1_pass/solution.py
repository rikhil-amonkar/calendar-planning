from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their details
    friends = {
        'Rebecca': {'location': 'Presidio', 'start': 18.25, 'end': 20.75, 'duration': 1.0},
        'Linda': {'location': 'Sunset District', 'start': 15.5, 'end': 19.75, 'duration': 0.5},
        'Elizabeth': {'location': 'Haight-Ashbury', 'start': 17.25, 'end': 19.5, 'duration': 1.75},
        'William': {'location': 'Mission District', 'start': 13.25, 'end': 19.5, 'duration': 0.5},
        'Robert': {'location': 'Golden Gate Park', 'start': 14.25, 'end': 21.5, 'duration': 0.75},
        'Mark': {'location': 'Russian Hill', 'start': 10.0, 'end': 21.25, 'duration': 1.25}
    }

    # Travel times matrix (in hours)
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

    # Create variables for each friend's meeting start and end times
    start_vars = {name: Real(f'start_{name}') for name in friends}
    end_vars = {name: Real(f'end_{name}') for name in friends}
    meet_vars = {name: Bool(f'meet_{name}') for name in friends}  # Whether to meet the friend

    # Initial location is The Castro at 9:00 AM (9.0 hours)
    current_time = 9.0
    current_location = 'The Castro'

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        s.add(Implies(meet_vars[name], start_vars[name] >= friend['start']))
        s.add(Implies(meet_vars[name], end_vars[name] <= friend['end']))
        s.add(Implies(meet_vars[name], end_vars[name] == start_vars[name] + friend['duration']))

    # Ensure no overlapping meetings and account for travel time
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                # If both meetings are scheduled, ensure they don't overlap
                s.add(Implies(And(meet_vars[name1], meet_vars[name2]),
                              Or(end_vars[name1] + travel_times[(friends[name1]['location'], friends[name2]['location'])] <= start_vars[name2],
                                 end_vars[name2] + travel_times[(friends[name2]['location'], friends[name1]['location'])] <= start_vars[name1])))

    # Ensure the first meeting starts after arriving at The Castro
    for name in friends:
        s.add(Implies(meet_vars[name], start_vars[name] >= current_time + travel_times[(current_location, friends[name]['location'])]))

    # Maximize the number of friends met
    objective = Sum([If(meet_vars[name], 1, 0) for name in friends])
    s.maximize(objective)

    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        print("Optimal Schedule:")
        scheduled = []
        for name in friends:
            if model.evaluate(meet_vars[name]):
                start = model.evaluate(start_vars[name])
                end = model.evaluate(end_vars[name])
                scheduled.append((name, float(start.as_fraction()), float(end.as_fraction())))
        
        # Sort by start time
        scheduled.sort(key=lambda x: x[1])
        
        for name, start, end in scheduled:
            start_str = f"{int(start)}:{int((start % 1) * 60):02d}"
            end_str = f"{int(end)}:{int((end % 1) * 60):02d}"
            print(f"Meet {name} at {friends[name]['location']} from {start_str} to {end_str}")
        
        print(f"Total friends met: {len(scheduled)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()