from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Friends and their details
    friends = {
        'Steven': {'location': 'North Beach', 'start': 17.5, 'end': 20.5, 'duration': 0.25},
        'Sarah': {'location': 'Golden Gate Park', 'start': 17.0, 'end': 19.25, 'duration': 1.25},
        'Brian': {'location': 'Embarcadero', 'start': 14.25, 'end': 16.0, 'duration': 1.75},
        'Stephanie': {'location': 'Haight-Ashbury', 'start': 10.25, 'end': 12.25, 'duration': 1.25},
        'Melissa': {'location': 'Richmond District', 'start': 14.0, 'end': 19.5, 'duration': 0.5},
        'Nancy': {'location': 'Nob Hill', 'start': 8.25, 'end': 12.75, 'duration': 1.5},
        'David': {'location': 'Marina District', 'start': 11.25, 'end': 13.25, 'duration': 2.0},
        'James': {'location': 'Presidio', 'start': 15.0, 'end': 18.25, 'duration': 2.0},
        'Elizabeth': {'location': 'Union Square', 'start': 11.5, 'end': 21.0, 'duration': 1.0},
        'Robert': {'location': 'Financial District', 'start': 13.25, 'end': 15.25, 'duration': 0.75}
    }

    # Travel times (simplified as a dictionary of dictionaries)
    travel_times = {
        'The Castro': {
            'North Beach': 20/60, 'Golden Gate Park': 11/60, 'Embarcadero': 22/60,
            'Haight-Ashbury': 6/60, 'Richmond District': 16/60, 'Nob Hill': 16/60,
            'Marina District': 21/60, 'Presidio': 20/60, 'Union Square': 19/60,
            'Financial District': 21/60
        },
        'North Beach': {
            'The Castro': 23/60, 'Golden Gate Park': 22/60, 'Embarcadero': 6/60,
            'Haight-Ashbury': 18/60, 'Richmond District': 18/60, 'Nob Hill': 7/60,
            'Marina District': 9/60, 'Presidio': 17/60, 'Union Square': 7/60,
            'Financial District': 8/60
        },
        'Golden Gate Park': {
            'The Castro': 13/60, 'North Beach': 23/60, 'Embarcadero': 25/60,
            'Haight-Ashbury': 7/60, 'Richmond District': 7/60, 'Nob Hill': 20/60,
            'Marina District': 16/60, 'Presidio': 11/60, 'Union Square': 22/60,
            'Financial District': 26/60
        },
        'Embarcadero': {
            'The Castro': 25/60, 'North Beach': 5/60, 'Golden Gate Park': 25/60,
            'Haight-Ashbury': 21/60, 'Richmond District': 21/60, 'Nob Hill': 10/60,
            'Marina District': 12/60, 'Presidio': 20/60, 'Union Square': 10/60,
            'Financial District': 5/60
        },
        'Haight-Ashbury': {
            'The Castro': 6/60, 'North Beach': 19/60, 'Golden Gate Park': 7/60,
            'Embarcadero': 20/60, 'Richmond District': 10/60, 'Nob Hill': 15/60,
            'Marina District': 17/60, 'Presidio': 15/60, 'Union Square': 19/60,
            'Financial District': 21/60
        },
        'Richmond District': {
            'The Castro': 16/60, 'North Beach': 17/60, 'Golden Gate Park': 9/60,
            'Embarcadero': 19/60, 'Haight-Ashbury': 10/60, 'Nob Hill': 17/60,
            'Marina District': 9/60, 'Presidio': 7/60, 'Union Square': 21/60,
            'Financial District': 22/60
        },
        'Nob Hill': {
            'The Castro': 17/60, 'North Beach': 8/60, 'Golden Gate Park': 17/60,
            'Embarcadero': 9/60, 'Haight-Ashbury': 13/60, 'Richmond District': 14/60,
            'Marina District': 11/60, 'Presidio': 17/60, 'Union Square': 7/60,
            'Financial District': 9/60
        },
        'Marina District': {
            'The Castro': 22/60, 'North Beach': 11/60, 'Golden Gate Park': 18/60,
            'Embarcadero': 14/60, 'Haight-Ashbury': 16/60, 'Richmond District': 11/60,
            'Nob Hill': 12/60, 'Presidio': 10/60, 'Union Square': 16/60,
            'Financial District': 17/60
        },
        'Presidio': {
            'The Castro': 21/60, 'North Beach': 18/60, 'Golden Gate Park': 12/60,
            'Embarcadero': 20/60, 'Haight-Ashbury': 15/60, 'Richmond District': 7/60,
            'Nob Hill': 18/60, 'Marina District': 11/60, 'Union Square': 22/60,
            'Financial District': 23/60
        },
        'Union Square': {
            'The Castro': 17/60, 'North Beach': 10/60, 'Golden Gate Park': 22/60,
            'Embarcadero': 11/60, 'Haight-Ashbury': 18/60, 'Richmond District': 20/60,
            'Nob Hill': 9/60, 'Marina District': 18/60, 'Presidio': 24/60,
            'Financial District': 9/60
        },
        'Financial District': {
            'The Castro': 20/60, 'North Beach': 7/60, 'Golden Gate Park': 23/60,
            'Embarcadero': 4/60, 'Haight-Ashbury': 19/60, 'Richmond District': 21/60,
            'Nob Hill': 8/60, 'Marina District': 15/60, 'Presidio': 22/60,
            'Union Square': 9/60
        }
    }

    # Create variables for each friend's meeting start and end times
    start_vars = {}
    end_vars = {}
    for name in friends:
        start_vars[name] = Real(f'start_{name}')
        end_vars[name] = Real(f'end_{name}')

    # Current location starts at The Castro at 9:00 AM (9.0 hours)
    current_time = 9.0
    current_location = 'The Castro'

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        s.add(start_vars[name] >= friend['start'])
        s.add(end_vars[name] <= friend['end'])
        s.add(end_vars[name] == start_vars[name] + friend['duration'])

    # Define the order of meetings (heuristic)
    meeting_order = ['Nancy', 'Stephanie', 'David', 'Elizabeth', 'Robert', 'Brian', 'James', 'Melissa', 'Sarah', 'Steven']

    # Add constraints based on the meeting order
    for i in range(len(meeting_order)):
        if i == 0:
            # First meeting: Nancy at Nob Hill
            s.add(start_vars[meeting_order[i]] >= current_time + travel_times[current_location][friends[meeting_order[i]]['location']])
        else:
            prev_friend = meeting_order[i-1]
            current_friend = meeting_order[i]
            travel_time = travel_times[friends[prev_friend]['location']][friends[current_friend]['location']]
            s.add(start_vars[current_friend] >= end_vars[prev_friend] + travel_time)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        schedule = []
        for name in meeting_order:
            start = m.evaluate(start_vars[name])
            end = m.evaluate(end_vars[name])
            # Convert start and end times to hours and minutes
            start_val = float(str(start))
            start_hour = int(start_val)
            start_min = int((start_val - start_hour) * 60)
            end_val = float(str(end))
            end_hour = int(end_val)
            end_min = int((end_val - end_hour) * 60)
            schedule.append((name, friends[name]['location'], start_hour, start_min, end_hour, end_min))
        # Sort the schedule by start time
        schedule.sort(key=lambda x: (x[2], x[3]))
        return schedule
    else:
        return None

schedule = solve_scheduling()
if schedule:
    print("SOLUTION:")
    for meeting in schedule:
        name, location, start_hour, start_min, end_hour, end_min = meeting
        print(f"Meet {name} at {location} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}")
else:
    print("No feasible schedule found.")