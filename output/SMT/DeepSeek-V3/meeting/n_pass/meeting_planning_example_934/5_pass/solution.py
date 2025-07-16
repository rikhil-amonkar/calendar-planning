from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Optimize()

    # Friends and their data
    friends = {
        'Mary': {'location': 'Embarcadero', 'start': 8*60, 'end': 21*60 + 15, 'min_duration': 75},
        'Kenneth': {'location': 'The Castro', 'start': 11*60 + 15, 'end': 19*60 + 15, 'min_duration': 30},
        'Joseph': {'location': 'Haight-Ashbury', 'start': 20*60, 'end': 22*60, 'min_duration': 120},
        'Sarah': {'location': 'Union Square', 'start': 11*60 + 45, 'end': 14*60 + 30, 'min_duration': 90},
        'Thomas': {'location': 'North Beach', 'start': 19*60 + 15, 'end': 19*60 + 45, 'min_duration': 15},
        'Daniel': {'location': 'Pacific Heights', 'start': 13*60 + 45, 'end': 20*60 + 30, 'min_duration': 15},
        'Richard': {'location': 'Chinatown', 'start': 8*60, 'end': 18*60 + 45, 'min_duration': 30},
        'Mark': {'location': 'Golden Gate Park', 'start': 17*60 + 30, 'end': 21*60 + 30, 'min_duration': 120},
        'David': {'location': 'Marina District', 'start': 20*60, 'end': 21*60, 'min_duration': 60},
        'Karen': {'location': 'Russian Hill', 'start': 13*60 + 15, 'end': 18*60 + 30, 'min_duration': 120}
    }

    # Create variables for each friend's meeting start and end times
    for name in friends:
        friends[name]['start_var'] = Int(f'start_{name}')
        friends[name]['end_var'] = Int(f'end_{name}')
        friends[name]['met'] = Bool(f'met_{name}')

    # Constraints for each friend
    for name in friends:
        data = friends[name]
        # Convert availability times to minutes since 9:00 AM (540 minutes)
        available_start = data['start'] - 540 if data['start'] >= 540 else 0
        available_end = data['end'] - 540
        
        s.add(Implies(friends[name]['met'], 
                     And(friends[name]['start_var'] >= available_start,
                         friends[name]['end_var'] <= available_end,
                         friends[name]['end_var'] - friends[name]['start_var'] >= data['min_duration'])))
        
        s.add(Implies(Not(friends[name]['met']), 
                     And(friends[name]['start_var'] == -1,
                         friends[name]['end_var'] == -1)))

    # Travel times dictionary
    travel_times = {
        ('Nob Hill', 'Embarcadero'): 9,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'Haight-Ashbury'): 13,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Golden Gate Park'): 17,
        ('Nob Hill', 'Marina District'): 11,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Embarcadero', 'The Castro'): 25,
        ('Embarcadero', 'Haight-Ashbury'): 21,
        ('Embarcadero', 'Union Square'): 10,
        ('Embarcadero', 'North Beach'): 5,
        ('Embarcadero', 'Pacific Heights'): 11,
        ('Embarcadero', 'Chinatown'): 7,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Marina District'): 12,
        ('Embarcadero', 'Russian Hill'): 8,
        ('The Castro', 'Haight-Ashbury'): 6,
        ('The Castro', 'Union Square'): 19,
        ('The Castro', 'North Beach'): 20,
        ('The Castro', 'Pacific Heights'): 16,
        ('The Castro', 'Chinatown'): 22,
        ('The Castro', 'Golden Gate Park'): 11,
        ('The Castro', 'Marina District'): 21,
        ('The Castro', 'Russian Hill'): 18,
        ('Haight-Ashbury', 'Union Square'): 19,
        ('Haight-Ashbury', 'North Beach'): 19,
        ('Haight-Ashbury', 'Pacific Heights'): 12,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'Russian Hill'): 13,
        ('North Beach', 'Pacific Heights'): 8,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Marina District'): 9,
        ('North Beach', 'Russian Hill'): 4,
        ('Pacific Heights', 'Chinatown'): 11,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Pacific Heights', 'Marina District'): 6,
        ('Pacific Heights', 'Russian Hill'): 7,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Marina District'): 12,
        ('Chinatown', 'Russian Hill'): 7,
        ('Golden Gate Park', 'Marina District'): 16,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Marina District', 'Russian Hill'): 8
    }

    # For each pair of friends, add constraints if both are met
    friend_names = list(friends.keys())
    for i in range(len(friend_names)):
        for j in range(i+1, len(friend_names)):
            name1 = friend_names[i]
            name2 = friend_names[j]
            loc1 = friends[name1]['location']
            loc2 = friends[name2]['location']
            
            # Get travel time (default to 10 if not found)
            travel_time = travel_times.get((loc1, loc2), 10)
            
            # Ensure meetings don't overlap considering travel time
            s.add(Implies(And(friends[name1]['met'], friends[name2]['met']),
                         Or(friends[name1]['end_var'] + travel_time <= friends[name2]['start_var'],
                            friends[name2]['end_var'] + travel_time <= friends[name1]['start_var'])))

    # Maximize the number of friends met
    s.maximize(Sum([If(friends[name]['met'], 1, 0) for name in friends]))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        # Print the schedule
        scheduled = []
        for name in friends:
            if m.evaluate(friends[name]['met']):
                start = m.evaluate(friends[name]['start_var']).as_long()
                end = m.evaluate(friends[name]['end_var']).as_long()
                start_hour = 9 + start // 60
                start_min = start % 60
                end_hour = 9 + end // 60
                end_min = end % 60
                scheduled.append((start, name, f"{start_hour}:{start_min:02d}", f"{end_hour}:{end_min:02d}"))
        
        scheduled.sort()
        for meet in scheduled:
            print(f"Meet {meet[1]} from {meet[2]} to {meet[3]} at {friends[meet[1]]['location']}")
        print(f"Total friends met: {len(scheduled)}")
    else:
        print("No solution found")

solve_scheduling()