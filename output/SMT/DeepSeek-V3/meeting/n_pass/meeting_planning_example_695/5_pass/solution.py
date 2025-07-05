from z3 import *

def solve_scheduling():
    # Initialize optimizer
    opt = Optimize()

    # Define friends and their details
    friends = [
        {
            'name': 'Paul',
            'location': 'Nob Hill',
            'available_start': 15 * 60 + 15,  # 4:15 PM
            'available_end': 21 * 60 + 15,    # 9:15 PM
            'min_duration': 60,
            'start': Int('Paul_start'),
            'end': Int('Paul_end'),
            'met': Int('Paul_met')
        },
        {
            'name': 'Carol',
            'location': 'Union Square',
            'available_start': 18 * 60,       # 6:00 PM
            'available_end': 20 * 60 + 15,   # 8:15 PM
            'min_duration': 120,
            'start': Int('Carol_start'),
            'end': Int('Carol_end'),
            'met': Int('Carol_met')
        },
        {
            'name': 'Patricia',
            'location': 'Chinatown',
            'available_start': 20 * 60,      # 8:00 PM
            'available_end': 21 * 60 + 30,    # 9:30 PM
            'min_duration': 75,
            'start': Int('Patricia_start'),
            'end': Int('Patricia_end'),
            'met': Int('Patricia_met')
        },
        {
            'name': 'Karen',
            'location': 'The Castro',
            'available_start': 17 * 60,      # 5:00 PM
            'available_end': 19 * 60,         # 7:00 PM
            'min_duration': 45,
            'start': Int('Karen_start'),
            'end': Int('Karen_end'),
            'met': Int('Karen_met')
        },
        {
            'name': 'Nancy',
            'location': 'Presidio',
            'available_start': 2 * 60 + 45,   # 11:45 AM
            'available_end': 22 * 60,         # 10:00 PM
            'min_duration': 30,
            'start': Int('Nancy_start'),
            'end': Int('Nancy_end'),
            'met': Int('Nancy_met')
        },
        {
            'name': 'Jeffrey',
            'location': 'Pacific Heights',
            'available_start': 20 * 60,       # 8:00 PM
            'available_end': 20 * 60 + 45,   # 8:45 PM
            'min_duration': 45,
            'start': Int('Jeffrey_start'),
            'end': Int('Jeffrey_end'),
            'met': Int('Jeffrey_met')
        },
        {
            'name': 'Matthew',
            'location': 'Russian Hill',
            'available_start': 15 * 60 + 45,  # 3:45 PM
            'available_end': 21 * 60 + 45,    # 9:45 PM
            'min_duration': 75,
            'start': Int('Matthew_start'),
            'end': Int('Matthew_end'),
            'met': Int('Matthew_met')
        }
    ]

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        'Bayview': {
            'Nob Hill': 20,
            'Union Square': 17,
            'Chinatown': 18,
            'The Castro': 20,
            'Presidio': 31,
            'Pacific Heights': 23,
            'Russian Hill': 23
        },
        'Nob Hill': {
            'Bayview': 19,
            'Union Square': 7,
            'Chinatown': 6,
            'The Castro': 17,
            'Presidio': 17,
            'Pacific Heights': 8,
            'Russian Hill': 5
        },
        'Union Square': {
            'Bayview': 15,
            'Nob Hill': 9,
            'Chinatown': 7,
            'The Castro': 19,
            'Presidio': 24,
            'Pacific Heights': 15,
            'Russian Hill': 13
        },
        'Chinatown': {
            'Bayview': 22,
            'Nob Hill': 8,
            'Union Square': 7,
            'The Castro': 22,
            'Presidio': 19,
            'Pacific Heights': 10,
            'Russian Hill': 7
        },
        'The Castro': {
            'Bayview': 19,
            'Nob Hill': 16,
            'Union Square': 19,
            'Chinatown': 20,
            'Presidio': 20,
            'Pacific Heights': 16,
            'Russian Hill': 18
        },
        'Presidio': {
            'Bayview': 31,
            'Nob Hill': 18,
            'Union Square': 22,
            'Chinatown': 21,
            'The Castro': 21,
            'Pacific Heights': 11,
            'Russian Hill': 14
        },
        'Pacific Heights': {
            'Bayview': 22,
            'Nob Hill': 8,
            'Union Square': 12,
            'Chinatown': 11,
            'The Castro': 16,
            'Presidio': 11,
            'Russian Hill': 7
        },
        'Russian Hill': {
            'Bayview': 23,
            'Nob Hill': 5,
            'Union Square': 11,
            'Chinatown': 9,
            'The Castro': 21,
            'Presidio': 14,
            'Pacific Heights': 7
        }
    }

    # For each friend, add constraints for meeting duration and availability
    for friend in friends:
        opt.add(friend['met'] == 0, friend['met'] == 1)  # Binary
        opt.add(Implies(friend['met'] == 1, 
                And(friend['start'] >= friend['available_start'],
                    friend['end'] <= friend['available_end'],
                    friend['end'] - friend['start'] >= friend['min_duration'])))

    # Ensure exactly 5 friends are met
    opt.add(Sum([friend['met'] for friend in friends]) == 5)

    # Add travel time constraints between consecutive meetings
    # We'll model this by requiring sufficient time between end of one meeting and start of next
    # This is a simplified approach - a more complete solution would sequence the meetings
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i != j:
                opt.add(Implies(And(friends[i]['met'] == 1, friends[j]['met'] == 1),
                          Or(friends[j]['start'] >= friends[i]['end'] + travel_times[friends[i]['location']][friends[j]['location']],
                             friends[i]['start'] >= friends[j]['end'] + travel_times[friends[j]['location']][friends[i]['location']])))

    # Check for a solution
    if opt.check() == sat:
        m = opt.model()
        print("Optimal Schedule:")
        scheduled_friends = []
        for friend in friends:
            if m[friend['met']].as_long() == 1:
                start = m[friend['start']].as_long()
                end = m[friend['end']].as_long()
                # Convert to actual time (minutes since 9:00 AM)
                start_hour = 9 + start // 60
                start_min = start % 60
                end_hour = 9 + end // 60
                end_min = end % 60
                # Format as 24-hour time
                start_time = f"{start_hour:02d}:{start_min:02d}"
                end_time = f"{end_hour:02d}:{end_min:02d}"
                scheduled_friends.append((start, friend['name'], friend['location'], start_time, end_time))
        # Sort by start time
        scheduled_friends.sort()
        for meeting in scheduled_friends:
            _, name, loc, start, end = meeting
            print(f"Meet {name} at {loc} from {start} to {end}")
        print(f"Total friends met: {len(scheduled_friends)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()