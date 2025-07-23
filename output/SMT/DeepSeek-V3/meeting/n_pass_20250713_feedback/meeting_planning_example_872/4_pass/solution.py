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

    # Create a list of all possible meeting orders
    friend_names = list(friends.keys())
    num_friends = len(friend_names)
    
    # Create variables for the meeting order
    order = [Int(f'order_{i}') for i in range(num_friends)]
    
    # Each order position must be between 0 and num_friends-1
    for o in order:
        s.add(o >= 0, o < num_friends)
    
    # All order positions must be distinct
    s.add(Distinct(order))
    
    # Add travel time constraints between consecutive meetings
    for i in range(1, num_friends):
        prev_idx = order[i-1]
        curr_idx = order[i]
        
        # Get the previous and current friend names
        prev_name = friend_names[prev_idx]
        curr_name = friend_names[curr_idx]
        
        # Get their locations
        prev_loc = friends[prev_name]['location']
        curr_loc = friends[curr_name]['location']
        
        # Get travel time
        travel_time = travel_times.get((prev_loc, curr_loc), 0)
        
        # Add constraint that current meeting starts after previous meeting ends plus travel time
        s.add(meeting_vars[curr_name]['start'] >= meeting_vars[prev_name]['end'] + travel_time)
    
    # First meeting must start after arrival time plus travel time from Presidio
    first_idx = order[0]
    first_name = friend_names[first_idx]
    first_loc = friends[first_name]['location']
    travel_time = travel_times.get(('Presidio', first_loc), 0)
    s.add(meeting_vars[first_name]['start'] >= current_time + travel_time)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        # Get the meeting order from the model
        meeting_order = [m[o].as_long() for o in order]
        for i in meeting_order:
            name = friend_names[i]
            start = m[meeting_vars[name]['start']].as_long()
            end = m[meeting_vars[name]['end']].as_long()
            print(f"Meet {name} at {friends[name]['location']} from {start//60:02d}:{start%60:02d} to {end//60:02d}:{end%60:02d}")
    else:
        print("No solution found")

solve_scheduling()