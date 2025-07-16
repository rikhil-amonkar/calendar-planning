from z3 import *

def solve_scheduling():
    s = Solver()

    # Define friends with their availability and desired meeting durations (in minutes)
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

    # Travel times between locations (in minutes)
    travel_times = {
        'Presidio': {'Haight-Ashbury': 15, 'Nob Hill': 18, 'Russian Hill': 14, 'North Beach': 18,
                    'Chinatown': 21, 'Union Square': 22, 'Embarcadero': 20, 'Financial District': 23, 'Marina District': 11},
        'Haight-Ashbury': {'Presidio': 15, 'Nob Hill': 15, 'Russian Hill': 17, 'North Beach': 19,
                          'Chinatown': 19, 'Union Square': 19, 'Embarcadero': 20, 'Financial District': 21, 'Marina District': 17},
        'Nob Hill': {'Presidio': 17, 'Haight-Ashbury': 13, 'Russian Hill': 5, 'North Beach': 8,
                    'Chinatown': 6, 'Union Square': 7, 'Embarcadero': 9, 'Financial District': 9, 'Marina District': 11},
        'Russian Hill': {'Presidio': 14, 'Haight-Ashbury': 17, 'Nob Hill': 5, 'North Beach': 5,
                        'Chinatown': 9, 'Union Square': 10, 'Embarcadero': 8, 'Financial District': 11, 'Marina District': 7},
        'North Beach': {'Presidio': 17, 'Haight-Ashbury': 18, 'Nob Hill': 7, 'Russian Hill': 4,
                       'Chinatown': 6, 'Union Square': 7, 'Embarcadero': 6, 'Financial District': 8, 'Marina District': 9},
        'Chinatown': {'Presidio': 19, 'Haight-Ashbury': 19, 'Nob Hill': 9, 'Russian Hill': 7,
                     'North Beach': 3, 'Union Square': 7, 'Embarcadero': 5, 'Financial District': 5, 'Marina District': 12},
        'Union Square': {'Presidio': 24, 'Haight-Ashbury': 18, 'Nob Hill': 9, 'Russian Hill': 13,
                        'North Beach': 10, 'Chinatown': 7, 'Embarcadero': 11, 'Financial District': 9, 'Marina District': 18},
        'Embarcadero': {'Presidio': 20, 'Haight-Ashbury': 21, 'Nob Hill': 10, 'Russian Hill': 8,
                       'North Beach': 5, 'Chinatown': 7, 'Union Square': 10, 'Financial District': 5, 'Marina District': 12},
        'Financial District': {'Presidio': 22, 'Haight-Ashbury': 19, 'Nob Hill': 8, 'Russian Hill': 11,
                             'North Beach': 7, 'Chinatown': 5, 'Union Square': 9, 'Embarcadero': 4, 'Marina District': 15},
        'Marina District': {'Presidio': 10, 'Haight-Ashbury': 16, 'Nob Hill': 12, 'Russian Hill': 8,
                           'North Beach': 11, 'Chinatown': 15, 'Union Square': 16, 'Embarcadero': 14, 'Financial District': 17}
    }

    # Create Z3 variables for meeting start times
    start_times = {name: Int(f'start_{name}') for name in friends}
    end_times = {name: Int(f'end_{name}') for name in friends}

    # Add basic meeting constraints
    for name in friends:
        s.add(start_times[name] >= friends[name]['start'])
        s.add(end_times[name] <= friends[name]['end'])
        s.add(end_times[name] == start_times[name] + friends[name]['duration'])

    # Define meeting order (this is a heuristic)
    meeting_order = ['Jason', 'Mark', 'Kenneth', 'Kimberly', 'Stephanie', 'Jessica', 'Brian', 'Karen', 'Steven']

    # Add travel time constraints between meetings
    prev_location = 'Presidio'
    prev_end = 9 * 60  # Start at 9:00 AM

    for name in meeting_order:
        # Get travel time from previous location to current meeting
        travel_time = travel_times[prev_location][friends[name]['location']]
        
        # Current meeting must start after previous meeting ends plus travel time
        s.add(start_times[name] >= prev_end + travel_time)
        
        # Update previous end time and location
        prev_end = end_times[name]
        prev_location = friends[name]['location']

    # Check if schedule is possible
    if s.check() == sat:
        model = s.model()
        schedule = []
        for name in meeting_order:
            start = model[start_times[name]].as_long()
            end = model[end_times[name]].as_long()
            schedule.append({
                'name': name,
                'location': friends[name]['location'],
                'start': f"{start//60}:{start%60:02d}",
                'end': f"{end//60}:{end%60:02d}"
            })
        return schedule
    else:
        return None

# Solve and print the schedule
schedule = solve_scheduling()
if schedule:
    print("SOLUTION:")
    for meeting in schedule:
        print(f"Meet {meeting['name']} at {meeting['location']} from {meeting['start']} to {meeting['end']}")
else:
    print("No feasible schedule found.")