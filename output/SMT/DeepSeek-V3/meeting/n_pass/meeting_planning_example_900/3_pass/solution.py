from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Define friends data
    friends = {
        'Matthew': {'location': 'The Castro', 'start': 16.5, 'end': 20.0, 'min_duration': 0.75},
        'Rebecca': {'location': 'Nob Hill', 'start': 15.25, 'end': 19.25, 'min_duration': 1.75},
        'Brian': {'location': 'Marina District', 'start': 14.25, 'end': 22.0, 'min_duration': 0.5},
        'Emily': {'location': 'Pacific Heights', 'start': 11.25, 'end': 19.75, 'min_duration': 0.25},
        'Karen': {'location': 'Haight-Ashbury', 'start': 11.75, 'end': 17.5, 'min_duration': 0.5},
        'Stephanie': {'location': 'Mission District', 'start': 13.0, 'end': 15.75, 'min_duration': 1.25},
        'James': {'location': 'Chinatown', 'start': 14.5, 'end': 19.0, 'min_duration': 2.0},
        'Steven': {'location': 'Russian Hill', 'start': 14.0, 'end': 20.0, 'min_duration': 0.5},
        'Elizabeth': {'location': 'Alamo Square', 'start': 13.0, 'end': 17.25, 'min_duration': 2.0},
        'William': {'location': 'Bayview', 'start': 18.25, 'end': 20.25, 'min_duration': 1.5}
    }

    # Travel times between locations (in hours)
    travel_times = {
        ('Richmond District', 'The Castro'): 16/60,
        ('Richmond District', 'Nob Hill'): 17/60,
        ('Richmond District', 'Marina District'): 9/60,
        ('Richmond District', 'Pacific Heights'): 10/60,
        ('Richmond District', 'Haight-Ashbury'): 10/60,
        ('Richmond District', 'Mission District'): 20/60,
        ('Richmond District', 'Chinatown'): 20/60,
        ('Richmond District', 'Russian Hill'): 13/60,
        ('Richmond District', 'Alamo Square'): 13/60,
        ('Richmond District', 'Bayview'): 27/60,
        ('The Castro', 'Nob Hill'): 16/60,
        ('The Castro', 'Marina District'): 21/60,
        ('The Castro', 'Pacific Heights'): 16/60,
        ('The Castro', 'Haight-Ashbury'): 6/60,
        ('The Castro', 'Mission District'): 7/60,
        ('The Castro', 'Chinatown'): 22/60,
        ('The Castro', 'Russian Hill'): 18/60,
        ('The Castro', 'Alamo Square'): 8/60,
        ('The Castro', 'Bayview'): 19/60,
        ('Nob Hill', 'Marina District'): 11/60,
        ('Nob Hill', 'Pacific Heights'): 8/60,
        ('Nob Hill', 'Haight-Ashbury'): 13/60,
        ('Nob Hill', 'Mission District'): 13/60,
        ('Nob Hill', 'Chinatown'): 6/60,
        ('Nob Hill', 'Russian Hill'): 5/60,
        ('Nob Hill', 'Alamo Square'): 11/60,
        ('Nob Hill', 'Bayview'): 19/60,
        ('Marina District', 'Pacific Heights'): 7/60,
        ('Marina District', 'Haight-Ashbury'): 16/60,
        ('Marina District', 'Mission District'): 20/60,
        ('Marina District', 'Chinatown'): 15/60,
        ('Marina District', 'Russian Hill'): 8/60,
        ('Marina District', 'Alamo Square'): 15/60,
        ('Marina District', 'Bayview'): 27/60,
        ('Pacific Heights', 'Haight-Ashbury'): 11/60,
        ('Pacific Heights', 'Mission District'): 15/60,
        ('Pacific Heights', 'Chinatown'): 11/60,
        ('Pacific Heights', 'Russian Hill'): 7/60,
        ('Pacific Heights', 'Alamo Square'): 10/60,
        ('Pacific Heights', 'Bayview'): 22/60,
        ('Haight-Ashbury', 'Mission District'): 11/60,
        ('Haight-Ashbury', 'Chinatown'): 19/60,
        ('Haight-Ashbury', 'Russian Hill'): 17/60,
        ('Haight-Ashbury', 'Alamo Square'): 5/60,
        ('Haight-Ashbury', 'Bayview'): 18/60,
        ('Mission District', 'Chinatown'): 16/60,
        ('Mission District', 'Russian Hill'): 15/60,
        ('Mission District', 'Alamo Square'): 11/60,
        ('Mission District', 'Bayview'): 14/60,
        ('Chinatown', 'Russian Hill'): 7/60,
        ('Chinatown', 'Alamo Square'): 17/60,
        ('Chinatown', 'Bayview'): 20/60,
        ('Russian Hill', 'Alamo Square'): 15/60,
        ('Russian Hill', 'Bayview'): 23/60,
        ('Alamo Square', 'Bayview'): 16/60
    }

    # Create variables
    meet_vars = {name: Bool(f'meet_{name}') for name in friends}
    start_vars = {name: Real(f'start_{name}') for name in friends}
    end_vars = {name: Real(f'end_{name}') for name in friends}

    # Current time and location
    current_time = 9.0  # 9:00 AM
    current_location = 'Richmond District'

    # Constraints for each friend
    for name in friends:
        data = friends[name]
        s.add(Implies(meet_vars[name], 
                     And(start_vars[name] >= data['start'],
                         end_vars[name] <= data['end'],
                         end_vars[name] - start_vars[name] >= data['min_duration'])))
        
        # If not meeting, set times to 0
        s.add(Implies(Not(meet_vars[name]), 
                     And(start_vars[name] == 0, end_vars[name] == 0)))

    # Travel time constraints
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                loc1 = friends[name1]['location']
                loc2 = friends[name2]['location']
                if (loc1, loc2) in travel_times:
                    travel = travel_times[(loc1, loc2)]
                elif (loc2, loc1) in travel_times:
                    travel = travel_times[(loc2, loc1)]
                else:
                    travel = 0  # Shouldn't happen with complete travel matrix
                
                s.add(Implies(And(meet_vars[name1], meet_vars[name2]),
                             Or(end_vars[name1] + travel <= start_vars[name2],
                                end_vars[name2] + travel <= start_vars[name1])))

    # First meeting must be after travel from starting location
    for name in friends:
        loc = friends[name]['location']
        if (current_location, loc) in travel_times:
            travel = travel_times[(current_location, loc)]
        else:
            travel = travel_times[(loc, current_location)]
        s.add(Implies(meet_vars[name], start_vars[name] >= current_time + travel))

    # Maximize number of friends met
    num_met = Sum([If(meet_vars[name], 1, 0) for name in friends])
    s.maximize(num_met)

    # Solve and print results
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule Found:")
        print(f"Total friends met: {m.evaluate(num_met)}")
        print("\nMeeting Schedule:")
        
        # Collect and sort meetings
        meetings = []
        for name in friends:
            if is_true(m.evaluate(meet_vars[name])):
                start = m.evaluate(start_vars[name])
                end = m.evaluate(end_vars[name])
                start_val = start.as_fraction() if is_rational_value(start) else float(start.as_decimal(3))
                end_val = end.as_fraction() if is_rational_value(end) else float(end.as_decimal(3))
                meetings.append((float(start_val), name, float(end_val), friends[name]['location']))
        
        # Sort by start time and print
        for meeting in sorted(meetings, key=lambda x: x[0]):
            start_h = int(meeting[0])
            start_m = int((meeting[0] - start_h) * 60)
            end_h = int(meeting[2])
            end_m = int((meeting[2] - end_h) * 60)
            print(f"{meeting[1]}: {start_h}:{start_m:02d} to {end_h}:{end_m:02d} at {meeting[3]}")
    else:
        print("No feasible schedule found.")

solve_scheduling()