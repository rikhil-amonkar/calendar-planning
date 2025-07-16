from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Locations and friends
    locations = ['Embarcadero', 'Golden Gate Park', 'Haight-Ashbury', 'Bayview', 'Presidio', 'Financial District']
    friends = {
        'Mary': {'location': 'Golden Gate Park', 'start': 8.75, 'end': 11.75, 'min_duration': 0.75},
        'Kevin': {'location': 'Haight-Ashbury', 'start': 10.25, 'end': 16.25, 'min_duration': 1.5},
        'Deborah': {'location': 'Bayview', 'start': 15.0, 'end': 19.25, 'min_duration': 2.0},
        'Stephanie': {'location': 'Presidio', 'start': 10.0, 'end': 17.25, 'min_duration': 2.0},
        'Emily': {'location': 'Financial District', 'start': 11.5, 'end': 21.75, 'min_duration': 1.75}
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        'Embarcadero': {
            'Golden Gate Park': 25,
            'Haight-Ashbury': 21,
            'Bayview': 21,
            'Presidio': 20,
            'Financial District': 5
        },
        'Golden Gate Park': {
            'Embarcadero': 25,
            'Haight-Ashbury': 7,
            'Bayview': 23,
            'Presidio': 11,
            'Financial District': 26
        },
        'Haight-Ashbury': {
            'Embarcadero': 20,
            'Golden Gate Park': 7,
            'Bayview': 18,
            'Presidio': 15,
            'Financial District': 21
        },
        'Bayview': {
            'Embarcadero': 19,
            'Golden Gate Park': 22,
            'Haight-Ashbury': 19,
            'Presidio': 31,
            'Financial District': 19
        },
        'Presidio': {
            'Embarcadero': 20,
            'Golden Gate Park': 12,
            'Haight-Ashbury': 15,
            'Bayview': 31,
            'Financial District': 23
        },
        'Financial District': {
            'Embarcadero': 4,
            'Golden Gate Park': 23,
            'Haight-Ashbury': 19,
            'Bayview': 19,
            'Presidio': 22
        }
    }

    # Convert travel times to hours
    for from_loc in travel_times:
        for to_loc in travel_times[from_loc]:
            travel_times[from_loc][to_loc] = travel_times[from_loc][to_loc] / 60.0

    # Variables for each friend: start time, end time, and whether they are met
    friend_vars = {}
    for name in friends:
        friend = friends[name]
        start_var = Real(f'start_{name}')
        end_var = Real(f'end_{name}')
        met_var = Bool(f'met_{name}')
        friend_vars[name] = {
            'start': start_var,
            'end': end_var,
            'met': met_var,
            'location': friend['location']
        }

    # Initial constraints: start at Embarcadero at 9:00 AM (9.0 hours)
    current_time = 9.0
    current_location = 'Embarcadero'  # Note: typo in the original, but we'll proceed with 'Embarcadero' as per the problem statement.

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        loc = friend['location']
        start_time = friend['start']
        end_time = friend['end']
        min_duration = friend['min_duration']
        vars = friend_vars[name]

        # If met, the meeting must be within the friend's availability and meet the duration
        s.add(Implies(vars['met'], And(
            vars['start'] >= start_time,
            vars['end'] <= end_time,
            vars['end'] - vars['start'] >= min_duration
        )))

        # If not met, start and end times are unconstrained (but we'll set them to 0 for clarity)
        s.add(Implies(Not(vars['met']), And(vars['start'] == 0, vars['end'] == 0)))

    # Order of meetings: we need to sequence them with travel times
    # We'll create a list of possible meetings and enforce ordering
    meeting_names = list(friends.keys())
    n = len(meeting_names)

    # Variables for the order: position[i] is the meeting at i-th position
    # We'll use integers to represent the order, but Z3 requires careful handling
    # Instead, we'll model the order by ensuring that for any two meetings, one is before or after the other with travel time

    # For each pair of distinct meetings, if both are met, then one must be after the other plus travel time
    for i in range(n):
        for j in range(i + 1, n):
            name_i = meeting_names[i]
            name_j = meeting_names[j]
            vars_i = friend_vars[name_i]
            vars_j = friend_vars[name_j]
            loc_i = vars_i['location']
            loc_j = vars_j['location']

            # Travel time from i to j
            travel_i_j = travel_times[loc_i][loc_j]
            # Travel time from j to i
            travel_j_i = travel_times[loc_j][loc_i]

            # Either i is before j or j is before i
            s.add(Implies(And(vars_i['met'], vars_j['met']),
                  Or(
                      vars_j['start'] >= vars_i['end'] + travel_i_j,
                      vars_i['start'] >= vars_j['end'] + travel_j_i
                  )))

    # The first meeting must start after current_time + travel time from Embarcadero to the meeting location
    for name in friends:
        vars = friend_vars[name]
        loc = vars['location']
        travel_time = travel_times['Embarcadero'][loc]
        s.add(Implies(vars['met'], vars['start'] >= current_time + travel_time))

    # Objective: maximize the number of friends met
    total_met = Sum([If(vars['met'], 1, 0) for name, vars in friend_vars.items()])
    s.maximize(total_met)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        scheduled_friends = 0
        schedule = []
        for name in friends:
            vars = friend_vars[name]
            if m.evaluate(vars['met']):
                scheduled_friends += 1
                start = m.evaluate(vars['start'])
                end = m.evaluate(vars['end'])
                start_val = start.as_fraction() if is_rational_value(start) else float(start.numerator_as_long())/float(start.denominator_as_long())
                end_val = end.as_fraction() if is_rational_value(end) else float(end.numerator_as_long())/float(end.denominator_as_long())
                start_hour = int(start_val)
                start_min = int((start_val - start_hour) * 60)
                end_hour = int(end_val)
                end_min = int((end_val - end_hour) * 60)
                schedule.append({
                    'name': name,
                    'location': vars['location'],
                    'start': f"{start_hour}:{start_min:02d}",
                    'end': f"{end_hour}:{end_min:02d}"
                })
        print(f"Total friends met: {scheduled_friends}")
        for entry in sorted(schedule, key=lambda x: x['start']):
            print(f"Meet {entry['name']} at {entry['location']} from {entry['start']} to {entry['end']}")
    else:
        print("No feasible schedule found.")

solve_scheduling()