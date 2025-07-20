from z3 import *
import json

def solve_scheduling_problem():
    # Define travel times between districts
    travel_times = {
        ('Marina District', 'Bayview'): 27,
        ('Marina District', 'Sunset District'): 19,
        ('Marina District', 'Richmond District'): 11,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Chinatown'): 15,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'North Beach'): 11,
        ('Marina District', 'Russian Hill'): 8,
        ('Marina District', 'Embarcadero'): 14,
        ('Bayview', 'Sunset District'): 23,
        ('Bayview', 'Richmond District'): 25,
        ('Bayview', 'Nob Hill'): 20,
        ('Bayview', 'Chinatown'): 19,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'North Beach'): 22,
        ('Bayview', 'Russian Hill'): 23,
        ('Bayview', 'Embarcadero'): 19,
        ('Sunset District', 'Richmond District'): 12,
        ('Sunset District', 'Nob Hill'): 27,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'North Beach'): 28,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'Embarcadero'): 30,
        ('Richmond District', 'Nob Hill'): 17,
        ('Richmond District', 'Chinatown'): 20,
        ('Richmond District', 'Haight-Ashbury'): 10,
        ('Richmond District', 'North Beach'): 17,
        ('Richmond District', 'Russian Hill'): 13,
        ('Richmond District', 'Embarcadero'): 19,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Haight-Ashbury'): 13,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Chinatown', 'Haight-Ashbury'): 19,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Russian Hill'): 7,
        ('Chinatown', 'Embarcadero'): 5,
        ('Haight-Ashbury', 'North Beach'): 19,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Haight-Ashbury', 'Embarcadero'): 20,
        ('North Beach', 'Russian Hill'): 4,
        ('North Beach', 'Embarcadero'): 6,
        ('Russian Hill', 'Embarcadero'): 8,
    }

    # Add symmetric travel times
    for (src, dst), time in list(travel_times.items()):
        if (dst, src) not in travel_times:
            travel_times[(dst, src)] = time

    # Friends' availability and meeting constraints
    friends = {
        'Charles': {'district': 'Bayview', 'start': 11.5, 'end': 14.5, 'duration': 0.75},
        'Robert': {'district': 'Sunset District', 'start': 16.75, 'end': 21.0, 'duration': 0.5},
        'Karen': {'district': 'Richmond District', 'start': 19.25, 'end': 21.5, 'duration': 1.0},
        'Rebecca': {'district': 'Nob Hill', 'start': 16.25, 'end': 20.5, 'duration': 1.5},
        'Margaret': {'district': 'Chinatown', 'start': 14.25, 'end': 19.75, 'duration': 2.0},
        'Patricia': {'district': 'Haight-Ashbury', 'start': 14.5, 'end': 20.5, 'duration': 0.75},
        'Mark': {'district': 'North Beach', 'start': 14.0, 'end': 18.5, 'duration': 1.75},
        'Melissa': {'district': 'Russian Hill', 'start': 13.0, 'end': 19.75, 'duration': 0.5},
        'Laura': {'district': 'Embarcadero', 'start': 7.75, 'end': 13.25, 'duration': 1.75},
    }

    # Initialize Z3 solver
    s = Optimize()

    # Create variables for each meeting's start and end times
    meeting_vars = {}
    for name in friends:
        start = Real(f'start_{name}')
        end = Real(f'end_{name}')
        meeting_vars[name] = {'start': start, 'end': end}

    # Add constraints for each meeting's time window and duration
    for name in friends:
        friend = friends[name]
        s.add(meeting_vars[name]['start'] >= friend['start'])
        s.add(meeting_vars[name]['end'] <= friend['end'])
        s.add(meeting_vars[name]['end'] - meeting_vars[name]['start'] >= friend['duration'])

    # Create order variables to determine meeting sequence
    num_friends = len(friends)
    order = {name: Int(f'order_{name}') for name in friends}
    s.add([And(order[name] >= 0, order[name] < num_friends) for name in friends])
    s.add(Distinct([order[name] for name in friends]))

    # Create variables for the start time of the entire schedule
    start_time = Real('start_time')
    s.add(start_time == 9.0)  # Start at 9:00 AM at Marina District

    # Add travel time constraints between consecutive meetings
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                s.add(Implies(
                    order[name1] + 1 == order[name2],
                    meeting_vars[name2]['start'] >= meeting_vars[name1]['end'] + 
                    travel_times.get((friends[name1]['district'], friends[name2]['district']), 0)
                ))

    # First meeting must be reachable from Marina District
    for name in friends:
        s.add(Implies(
            order[name] == 0,
            meeting_vars[name]['start'] >= start_time + travel_times.get(
                ('Marina District', friends[name]['district']), 0)
        ))

    # Maximize the number of friends met
    met = [Int(f'met_{name}') for name in friends]
    for name in friends:
        s.add(met[order[name]] == If(
            And(meeting_vars[name]['end'] - meeting_vars[name]['start'] >= friends[name]['duration'],
                meeting_vars[name]['start'] >= friends[name]['start'],
                meeting_vars[name]['end'] <= friends[name]['end']),
            1, 0))
    total_met = sum(met)
    s.maximize(total_met)

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in friends:
            start = model[meeting_vars[name]['start']]
            end = model[meeting_vars[name]['end']]
            order_val = model[order[name]].as_long()
            
            # Convert to float if possible
            try:
                start_time = float(str(start))
                end_time = float(str(end))
            except:
                if is_rational_value(start):
                    start_time = float(start.numerator_as_long())/float(start.denominator_as_long())
                    end_time = float(end.numerator_as_long())/float(end.denominator_as_long())
                else:
                    # Fallback for other cases
                    start_time = 0
                    end_time = 0

            # Convert decimal hours to HH:MM format
            start_hh = int(start_time)
            start_mm = int((start_time - start_hh) * 60)
            end_hh = int(end_time)
            end_mm = int((end_time - end_hh) * 60)
            
            itinerary.append({
                'order': order_val,
                'action': 'meet',
                'person': name,
                'start_time': f"{start_hh:02d}:{start_mm:02d}",
                'end_time': f"{end_hh:02d}:{end_mm:02d}",
                'location': friends[name]['district']
            })

        # Sort itinerary by order
        itinerary.sort(key=lambda x: x['order'])
        # Remove order field from final output
        final_itinerary = [{'action': item['action'], 
                          'person': item['person'],
                          'start_time': item['start_time'],
                          'end_time': item['end_time']} 
                         for item in itinerary]
        return {'itinerary': final_itinerary}
    else:
        return {'itinerary': []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))