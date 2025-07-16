from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Locations and friends data
    friends = {
        'Mary': {'location': 'Golden Gate Park', 'start': 8.75, 'end': 11.75, 'min_duration': 0.75},
        'Kevin': {'location': 'Haight-Ashbury', 'start': 10.25, 'end': 16.25, 'min_duration': 1.5},
        'Deborah': {'location': 'Bayview', 'start': 15.0, 'end': 19.25, 'min_duration': 2.0},
        'Stephanie': {'location': 'Presidio', 'start': 10.0, 'end': 17.25, 'min_duration': 2.0},
        'Emily': {'location': 'Financial District', 'start': 11.5, 'end': 21.75, 'min_duration': 1.75}
    }

    # Travel times in minutes converted to hours
    travel_times = {
        'Embarcadero': {
            'Golden Gate Park': 25/60,
            'Haight-Ashbury': 21/60,
            'Bayview': 21/60,
            'Presidio': 20/60,
            'Financial District': 5/60
        },
        'Golden Gate Park': {
            'Embarcadero': 25/60,
            'Haight-Ashbury': 7/60,
            'Bayview': 23/60,
            'Presidio': 11/60,
            'Financial District': 26/60
        },
        'Haight-Ashbury': {
            'Embarcadero': 20/60,
            'Golden Gate Park': 7/60,
            'Bayview': 18/60,
            'Presidio': 15/60,
            'Financial District': 21/60
        },
        'Bayview': {
            'Embarcadero': 19/60,
            'Golden Gate Park': 22/60,
            'Haight-Ashbury': 19/60,
            'Presidio': 31/60,
            'Financial District': 19/60
        },
        'Presidio': {
            'Embarcadero': 20/60,
            'Golden Gate Park': 12/60,
            'Haight-Ashbury': 15/60,
            'Bayview': 31/60,
            'Financial District': 23/60
        },
        'Financial District': {
            'Embarcadero': 4/60,
            'Golden Gate Park': 23/60,
            'Haight-Ashbury': 19/60,
            'Bayview': 19/60,
            'Presidio': 22/60
        }
    }

    # Create variables for each friend
    friend_vars = {}
    for name in friends:
        start = Real(f'start_{name}')
        end = Real(f'end_{name}')
        met = Bool(f'met_{name}')
        friend_vars[name] = {
            'start': start,
            'end': end,
            'met': met,
            'location': friends[name]['location']
        }

    # Starting point
    current_time = 9.0  # 9:00 AM
    current_location = 'Embarcadero'

    # Add constraints for each friend
    for name in friends:
        friend = friends[name]
        vars = friend_vars[name]
        
        # If meeting this friend, it must be within their window and duration
        s.add(Implies(vars['met'], And(
            vars['start'] >= friend['start'],
            vars['end'] <= friend['end'],
            vars['end'] - vars['start'] >= friend['min_duration']
        )))
        
        # If not meeting, set times to 0
        s.add(Implies(Not(vars['met']), And(vars['start'] == 0, vars['end'] == 0)))

    # Sequence constraints with travel times
    meeting_names = list(friends.keys())
    for i in range(len(meeting_names)):
        for j in range(i+1, len(meeting_names)):
            name1 = meeting_names[i]
            name2 = meeting_names[j]
            vars1 = friend_vars[name1]
            vars2 = friend_vars[name2]
            
            # Travel time between locations
            travel = travel_times[vars1['location']][vars2['location']]
            travel_rev = travel_times[vars2['location']][vars1['location']]
            
            # Either meeting1 is before meeting2 or vice versa
            s.add(Implies(And(vars1['met'], vars2['met']),
                  Or(
                      vars2['start'] >= vars1['end'] + travel,
                      vars1['start'] >= vars2['end'] + travel_rev
                  )))

    # First meeting must be after travel time from starting point
    for name in friends:
        vars = friend_vars[name]
        travel = travel_times[current_location][vars['location']]
        s.add(Implies(vars['met'], vars['start'] >= current_time + travel))

    # Objective: maximize number of friends met
    total_met = Sum([If(vars['met'], 1, 0) for vars in friend_vars.values()])
    s.maximize(total_met)

    # Solve and print results
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        scheduled = []
        for name in friends:
            vars = friend_vars[name]
            if is_true(m.evaluate(vars['met'])):
                start = m.evaluate(vars['start'])
                end = m.evaluate(vars['end'])
                
                # Convert to hours:minutes format
                def to_time(val):
                    if is_rational_value(val):
                        val = val.as_fraction()
                    else:
                        val = float(val.numerator_as_long())/float(val.denominator_as_long())
                    hours = int(val)
                    minutes = int((val - hours) * 60)
                    return f"{hours}:{minutes:02d}"
                
                scheduled.append({
                    'name': name,
                    'location': vars['location'],
                    'start': to_time(start),
                    'end': to_time(end)
                })
        
        # Sort by start time
        scheduled.sort(key=lambda x: x['start'])
        
        print(f"Total friends met: {len(scheduled)}")
        for meeting in scheduled:
            print(f"Meet {meeting['name']} at {meeting['location']} from {meeting['start']} to {meeting['end']}")
    else:
        print("No feasible schedule found.")

solve_scheduling()