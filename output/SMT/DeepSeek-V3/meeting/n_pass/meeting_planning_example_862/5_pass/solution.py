from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Friend data (times in hours)
    friends = {
        'Laura': {'location': 'Alamo Square', 'start': 14.5, 'end': 16.25, 'min_duration': 75/60},
        'Brian': {'location': 'Presidio', 'start': 10.25, 'end': 17.0, 'min_duration': 30/60},
        'Karen': {'location': 'Russian Hill', 'start': 18.0, 'end': 20.25, 'min_duration': 90/60},
        'Stephanie': {'location': 'North Beach', 'start': 10.25, 'end': 16.0, 'min_duration': 75/60},
        'Helen': {'location': 'Golden Gate Park', 'start': 11.5, 'end': 21.75, 'min_duration': 120/60},
        'Sandra': {'location': 'Richmond District', 'start': 8.0, 'end': 15.25, 'min_duration': 30/60},
        'Mary': {'location': 'Embarcadero', 'start': 16.75, 'end': 18.75, 'min_duration': 120/60},
        'Deborah': {'location': 'Financial District', 'start': 19.0, 'end': 20.75, 'min_duration': 105/60},
        'Elizabeth': {'location': 'Marina District', 'start': 8.5, 'end': 13.25, 'min_duration': 105/60},
    }

    # Travel times in hours
    travel_times = {
        ('Mission District', 'Alamo Square'): 11/60,
        ('Mission District', 'Presidio'): 25/60,
        # ... (include all other travel times from previous versions)
    }

    # Create meeting variables
    meeting_starts = {name: Real(f'start_{name}') for name in friends}
    meeting_ends = {name: Real(f'end_{name}') for name in friends}
    meet_flags = {name: Bool(f'meet_{name}') for name in friends}

    # Starting point
    current_time = 9.0
    current_location = 'Mission District'

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        start = meeting_starts[name]
        end = meeting_ends[name]
        meet = meet_flags[name]

        # If meeting happens, it must be within availability window
        s.add(Implies(meet, start >= friend['start']))
        s.add(Implies(meet, end <= friend['end']))
        
        # Meeting duration must satisfy minimum requirement
        s.add(Implies(meet, end - start >= friend['min_duration']))

    # Meeting order constraints
    all_friends = list(friends.keys())
    for i in range(len(all_friends)):
        for j in range(i+1, len(all_friends)):
            f1 = all_friends[i]
            f2 = all_friends[j]
            
            # Either f1 is before f2 or vice versa
            s.add(Or(
                And(meet_flags[f1], meet_flags[f2], meeting_ends[f1] + travel_times[(friends[f1]['location'], friends[f2]['location'])] <= meeting_starts[f2]),
                And(meet_flags[f1], meet_flags[f2], meeting_ends[f2] + travel_times[(friends[f2]['location'], friends[f1]['location'])] <= meeting_starts[f1]),
                Not(meet_flags[f1]),
                Not(meet_flags[f2])
            ))

    # First meeting must account for initial travel
    for name in friends:
        travel_time = travel_times[(current_location, friends[name]['location'])]
        s.add(Implies(meet_flags[name], meeting_starts[name] >= current_time + travel_time))

    # Maximize number of friends met
    s.maximize(Sum([If(meet_flags[name], 1, 0) for name in friends]))

    # Solve
    if s.check() == sat:
        model = s.model()
        schedule = []
        
        for name in friends:
            if is_true(model[meet_flags[name]]):
                start = model[meeting_starts[name]].as_fraction()
                end = model[meeting_ends[name]].as_fraction()
                
                start_hr = float(start.numerator) / float(start.denominator)
                end_hr = float(end.numerator) / float(end.denominator)
                
                schedule.append((name, start_hr, end_hr))
        
        # Sort by start time
        schedule.sort(key=lambda x: x[1])
        
        # Print schedule
        print("SOLUTION:")
        for name, start, end in schedule:
            start_hr = int(start)
            start_min = int(round((start - start_hr) * 60))
            end_hr = int(end)
            end_min = int(round((end - end_hr) * 60))
            
            print(f"Meet {name} at {friends[name]['location']} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}")
    else:
        print("No valid schedule found")

solve_scheduling()