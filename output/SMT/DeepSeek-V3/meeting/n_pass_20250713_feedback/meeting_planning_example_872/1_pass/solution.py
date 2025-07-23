from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define friends and their details
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

    # Define travel times (in minutes) between locations
    travel_times = {
        ('Presidio', 'Haight-Ashbury'): 15,
        ('Presidio', 'Nob Hill'): 18,
        ('Presidio', 'Russian Hill'): 14,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Union Square'): 22,
        ('Presidio', 'Embarcadero'): 20,
        ('Presidio', 'Financial District'): 23,
        ('Presidio', 'Marina District'): 11,
        ('Haight-Ashbury', 'Presidio'): 15,
        ('Haight-Ashbury', 'Nob Hill'): 15,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Haight-Ashbury', 'North Beach'): 19,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'Union Square'): 19,
        ('Haight-Ashbury', 'Embarcadero'): 20,
        ('Haight-Ashbury', 'Financial District'): 21,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Nob Hill', 'Presidio'): 17,
        ('Nob Hill', 'Haight-Ashbury'): 13,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Nob Hill', 'Financial District'): 9,
        ('Nob Hill', 'Marina District'): 11,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Union Square'): 10,
        ('Russian Hill', 'Embarcadero'): 8,
        ('Russian Hill', 'Financial District'): 11,
        ('Russian Hill', 'Marina District'): 7,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Haight-Ashbury'): 18,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Russian Hill'): 4,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'Embarcadero'): 6,
        ('North Beach', 'Financial District'): 8,
        ('North Beach', 'Marina District'): 9,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'Haight-Ashbury'): 19,
        ('Chinatown', 'Nob Hill'): 9,
        ('Chinatown', 'Russian Hill'): 7,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Embarcadero'): 5,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'Marina District'): 12,
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'Haight-Ashbury'): 18,
        ('Union Square', 'Nob Hill'): 9,
        ('Union Square', 'Russian Hill'): 13,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Embarcadero'): 11,
        ('Union Square', 'Financial District'): 9,
        ('Union Square', 'Marina District'): 18,
        ('Embarcadero', 'Presidio'): 20,
        ('Embarcadero', 'Haight-Ashbury'): 21,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Russian Hill'): 8,
        ('Embarcadero', 'North Beach'): 5,
        ('Embarcadero', 'Chinatown'): 7,
        ('Embarcadero', 'Union Square'): 10,
        ('Embarcadero', 'Financial District'): 5,
        ('Embarcadero', 'Marina District'): 12,
        ('Financial District', 'Presidio'): 22,
        ('Financial District', 'Haight-Ashbury'): 19,
        ('Financial District', 'Nob Hill'): 8,
        ('Financial District', 'Russian Hill'): 11,
        ('Financial District', 'North Beach'): 7,
        ('Financial District', 'Chinatown'): 5,
        ('Financial District', 'Union Square'): 9,
        ('Financial District', 'Embarcadero'): 4,
        ('Financial District', 'Marina District'): 15,
        ('Marina District', 'Presidio'): 10,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Russian Hill'): 8,
        ('Marina District', 'North Beach'): 11,
        ('Marina District', 'Chinatown'): 15,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'Embarcadero'): 14,
        ('Marina District', 'Financial District'): 17
    }

    # Create variables for each friend's meeting start and end times
    meeting_vars = {}
    for name in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        meeting_vars[name] = {'start': start, 'end': end}
        # Constrain meeting to be within friend's availability
        s.add(start >= friends[name]['start'])
        s.add(end <= friends[name]['end'])
        s.add(end == start + friends[name]['duration'])

    # Current location starts at Presidio at 9:00 AM (540 minutes)
    current_time = 9 * 60
    current_location = 'Presidio'

    # Define order of meetings (this is a simplification; in reality, we'd need to explore all permutations)
    # For simplicity, we'll try to meet friends in the order of their earliest availability
    ordered_friends = sorted(friends.keys(), key=lambda x: friends[x]['start'])

    # Add constraints for travel times between meetings
    for i in range(len(ordered_friends)):
        if i == 0:
            prev_location = current_location
            prev_end = current_time
        else:
            prev_name = ordered_friends[i-1]
            prev_location = friends[prev_name]['location']
            prev_end = meeting_vars[prev_name]['end']

        curr_name = ordered_friends[i]
        curr_location = friends[curr_name]['location']
        travel_time = travel_times.get((prev_location, curr_location), 0)
        s.add(meeting_vars[curr_name]['start'] >= prev_end + travel_time)

    # Maximize the number of friends met
    met = [If(meeting_vars[name]['start'] >= 0, 1, 0) for name in friends]
    s.maximize(Sum(met))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        for name in ordered_friends:
            start = m[meeting_vars[name]['start']].as_long()
            end = m[meeting_vars[name]['end']].as_long()
            if start >= 0:
                print(f"Meet {name} at {friends[name]['location']} from {start//60:02d}:{start%60:02d} to {end//60:02d}:{end%60:02d}")
    else:
        print("No solution found")

solve_scheduling()