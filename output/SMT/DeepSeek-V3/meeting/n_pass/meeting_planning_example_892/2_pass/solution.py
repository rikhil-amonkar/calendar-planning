from z3 import *
import json

def solve_scheduling_problem():
    # Define the travel times between districts
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
        ('Bayview', 'Marina District'): 27,
        ('Bayview', 'Sunset District'): 23,
        ('Bayview', 'Richmond District'): 25,
        ('Bayview', 'Nob Hill'): 20,
        ('Bayview', 'Chinatown'): 19,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'North Beach'): 22,
        ('Bayview', 'Russian Hill'): 23,
        ('Bayview', 'Embarcadero'): 19,
        ('Sunset District', 'Marina District'): 21,
        ('Sunset District', 'Bayview'): 22,
        ('Sunset District', 'Richmond District'): 12,
        ('Sunset District', 'Nob Hill'): 27,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'North Beach'): 28,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'Embarcadero'): 30,
        ('Richmond District', 'Marina District'): 9,
        ('Richmond District', 'Bayview'): 27,
        ('Richmond District', 'Sunset District'): 11,
        ('Richmond District', 'Nob Hill'): 17,
        ('Richmond District', 'Chinatown'): 20,
        ('Richmond District', 'Haight-Ashbury'): 10,
        ('Richmond District', 'North Beach'): 17,
        ('Richmond District', 'Russian Hill'): 13,
        ('Richmond District', 'Embarcadero'): 19,
        ('Nob Hill', 'Marina District'): 11,
        ('Nob Hill', 'Bayview'): 19,
        ('Nob Hill', 'Sunset District'): 24,
        ('Nob Hill', 'Richmond District'): 14,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Haight-Ashbury'): 13,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Chinatown', 'Marina District'): 12,
        ('Chinatown', 'Bayview'): 20,
        ('Chinatown', 'Sunset District'): 29,
        ('Chinatown', 'Richmond District'): 20,
        ('Chinatown', 'Nob Hill'): 9,
        ('Chinatown', 'Haight-Ashbury'): 19,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Russian Hill'): 7,
        ('Chinatown', 'Embarcadero'): 5,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Haight-Ashbury', 'Richmond District'): 10,
        ('Haight-Ashbury', 'Nob Hill'): 15,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'North Beach'): 19,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Haight-Ashbury', 'Embarcadero'): 20,
        ('North Beach', 'Marina District'): 9,
        ('North Beach', 'Bayview'): 25,
        ('North Beach', 'Sunset District'): 27,
        ('North Beach', 'Richmond District'): 18,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Haight-Ashbury'): 18,
        ('North Beach', 'Russian Hill'): 4,
        ('North Beach', 'Embarcadero'): 6,
        ('Russian Hill', 'Marina District'): 7,
        ('Russian Hill', 'Bayview'): 23,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Richmond District'): 14,
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Embarcadero'): 8,
        ('Embarcadero', 'Marina District'): 12,
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Sunset District'): 30,
        ('Embarcadero', 'Richmond District'): 21,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Chinatown'): 7,
        ('Embarcadero', 'Haight-Ashbury'): 21,
        ('Embarcadero', 'North Beach'): 5,
        ('Embarcadero', 'Russian Hill'): 8,
    }

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
    s = Solver()

    # Create variables for each meeting's start and end times
    meeting_vars = {}
    for name in friends:
        start = Real(f'start_{name}')
        end = Real(f'end_{name}')
        meeting_vars[name] = {'start': start, 'end': end}

    # Add constraints for each meeting
    for name in friends:
        friend = friends[name]
        s.add(meeting_vars[name]['start'] >= friend['start'])
        s.add(meeting_vars[name]['end'] <= friend['end'])
        s.add(meeting_vars[name]['end'] - meeting_vars[name]['start'] >= friend['duration'])

    # Initial location is Marina District at 9:00 AM
    current_time = 9.0
    current_location = 'Marina District'

    # Ensure meetings are scheduled in order with travel time
    # We'll let the solver choose the order, but ensure that travel times are respected
    # To do this, we'll add constraints for all possible transitions
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                travel_time = travel_times.get((friends[name1]['district'], friends[name2]['district']), 0)
                s.add(Implies(
                    meeting_vars[name1]['end'] + travel_time <= meeting_vars[name2]['start'],
                    True
                ))

    # Additionally, ensure that the first meeting starts after arriving at Marina District
    for name in friends:
        travel_time = travel_times.get((current_location, friends[name]['district']), 0)
        s.add(meeting_vars[name]['start'] >= current_time + travel_time)

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in friends:
            start = model[meeting_vars[name]['start']]
            end = model[meeting_vars[name]['end']]
            start_time = float(start.as_fraction())
            end_time = float(end.as_fraction())
            # Convert decimal hours to HH:MM format
            start_hh = int(start_time)
            start_mm = int((start_time - start_hh) * 60)
            end_hh = int(end_time)
            end_mm = int((end_time - end_hh) * 60)
            itinerary.append({
                'action': 'meet',
                'person': name,
                'start_time': f"{start_hh:02d}:{start_mm:02d}",
                'end_time': f"{end_hh:02d}:{end_mm:02d}"
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {'itinerary': itinerary}
    else:
        return {'itinerary': []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))