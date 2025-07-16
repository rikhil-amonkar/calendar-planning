from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their details (times in minutes since midnight)
    friends = {
        'Karen': {'location': 'Haight-Ashbury', 'start': 21*60, 'end': 21*60 + 45, 'duration': 45},
        'Jessica': {'location': 'Nob Hill', 'start': 13*60 + 45, 'end': 21*60, 'duration': 90},
        'Brian': {'location': 'Russian Hill', 'start': 15*60 + 30, 'end': 21*60 + 45, 'duration': 60},
        'Kenneth': {'location': 'North Beach', 'start': 9*60 + 45, 'end': 21*60, 'duration': 30},
        'Jason': {'location': 'Chinatown', 'start': 8*60 + 15, 'end': 11*60 + 45, 'duration': 75},
        'Stephanie': {'location': 'Union Square', 'start': 14*60 + 45, 'end': 18*60 + 45, 'duration': 105},
        'Kimberly': {'location': 'Embarcadero', 'start': 9*60 + 45, 'end': 19*60 + 30, 'duration': 75},
        'Steven': {'location': 'Financial District', 'start': 7*60 + 15, 'end': 21*60 + 15, 'duration': 60},
        'Mark': {'location': 'Marina District', 'start': 10*60 + 15, 'end': 13*60, 'duration': 75}
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        'Presidio': {
            'Haight-Ashbury': 15, 'Nob Hill': 18, 'Russian Hill': 14, 'North Beach': 18,
            'Chinatown': 21, 'Union Square': 22, 'Embarcadero': 20, 'Financial District': 23, 'Marina District': 11
        },
        'Haight-Ashbury': {
            'Presidio': 15, 'Nob Hill': 15, 'Russian Hill': 17, 'North Beach': 19,
            'Chinatown': 19, 'Union Square': 19, 'Embarcadero': 20, 'Financial District': 21, 'Marina District': 17
        },
        'Nob Hill': {
            'Presidio': 17, 'Haight-Ashbury': 13, 'Russian Hill': 5, 'North Beach': 8,
            'Chinatown': 6, 'Union Square': 7, 'Embarcadero': 9, 'Financial District': 9, 'Marina District': 11
        },
        'Russian Hill': {
            'Presidio': 14, 'Haight-Ashbury': 17, 'Nob Hill': 5, 'North Beach': 5,
            'Chinatown': 9, 'Union Square': 10, 'Embarcadero': 8, 'Financial District': 11, 'Marina District': 7
        },
        'North Beach': {
            'Presidio': 17, 'Haight-Ashbury': 18, 'Nob Hill': 7, 'Russian Hill': 4,
            'Chinatown': 6, 'Union Square': 7, 'Embarcadero': 6, 'Financial District': 8, 'Marina District': 9
        },
        'Chinatown': {
            'Presidio': 19, 'Haight-Ashbury': 19, 'Nob Hill': 9, 'Russian Hill': 7,
            'North Beach': 3, 'Union Square': 7, 'Embarcadero': 5, 'Financial District': 5, 'Marina District': 12
        },
        'Union Square': {
            'Presidio': 24, 'Haight-Ashbury': 18, 'Nob Hill': 9, 'Russian Hill': 13,
            'North Beach': 10, 'Chinatown': 7, 'Embarcadero': 11, 'Financial District': 9, 'Marina District': 18
        },
        'Embarcadero': {
            'Presidio': 20, 'Haight-Ashbury': 21, 'Nob Hill': 10, 'Russian Hill': 8,
            'North Beach': 5, 'Chinatown': 7, 'Union Square': 10, 'Financial District': 5, 'Marina District': 12
        },
        'Financial District': {
            'Presidio': 22, 'Haight-Ashbury': 19, 'Nob Hill': 8, 'Russian Hill': 11,
            'North Beach': 7, 'Chinatown': 5, 'Union Square': 9, 'Embarcadero': 4, 'Marina District': 15
        },
        'Marina District': {
            'Presidio': 10, 'Haight-Ashbury': 16, 'Nob Hill': 12, 'Russian Hill': 8,
            'North Beach': 11, 'Chinatown': 15, 'Union Square': 16, 'Embarcadero': 14, 'Financial District': 17
        }
    }

    # Create variables for each friend's meeting start time
    start_vars = {name: Int(f'start_{name}') for name in friends}
    end_vars = {name: Int(f'end_{name}') for name in friends}

    # Constraints for each meeting
    for name in friends:
        friend = friends[name]
        s.add(start_vars[name] >= friend['start'])
        s.add(end_vars[name] <= friend['end'])
        s.add(end_vars[name] == start_vars[name] + friend['duration'])

    # Current time and location
    current_time = 9 * 60  # 9:00 AM in minutes
    current_location = 'Presidio'

    # We'll try to meet friends in this order (this is a heuristic)
    meeting_order = ['Jason', 'Mark', 'Kenneth', 'Kimberly', 'Stephanie', 'Jessica', 'Brian', 'Karen', 'Steven']

    # Add travel time constraints between meetings
    for i in range(len(meeting_order)):
        if i == 0:
            prev_end = current_time
            prev_loc = current_location
        else:
            prev_name = meeting_order[i-1]
            prev_end = end_vars[prev_name]
            prev_loc = friends[prev_name]['location']

        current_name = meeting_order[i]
        travel_time = travel_times[prev_loc][friends[current_name]['location']]
        s.add(start_vars[current_name] >= prev_end + travel_time)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        schedule = []
        for name in meeting_order:
            start = model[start_vars[name]].as_long()
            end = model[end_vars[name]].as_long()
            schedule.append({
                'name': name,
                'location': friends[name]['location'],
                'start': f"{start//60}:{start%60:02d}",
                'end': f"{end//60}:{end%60:02d}"
            })
        return schedule
    else:
        return None

schedule = solve_scheduling()
if schedule:
    print("SOLUTION:")
    for meeting in schedule:
        print(f"Meet {meeting['name']} at {meeting['location']} from {meeting['start']} to {meeting['end']}")
else:
    print("No feasible schedule found.")