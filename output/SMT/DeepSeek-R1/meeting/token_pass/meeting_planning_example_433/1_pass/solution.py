from z3 import *
import json

def main():
    # Convert all times to minutes from midnight
    base_time = 9 * 60  # 9:00 AM in minutes from midnight

    # Time windows in minutes from midnight
    windows = {
        'Emily': (19 * 60, 21 * 60),
        'Margaret': (16 * 60 + 30, 20 * 60 + 15),
        'Ronald': (18 * 60 + 30, 19 * 60 + 30),
        'Deborah': (13 * 60 + 45, 21 * 60 + 15),
        'Jeffrey': (11 * 60 + 15, 14 * 60 + 30)
    }

    min_durations = {
        'Emily': 15,
        'Margaret': 75,
        'Ronald': 45,
        'Deborah': 90,
        'Jeffrey': 120
    }

    location_indices = {
        'Emily': 1,
        'Margaret': 2,
        'Ronald': 3,
        'Deborah': 4,
        'Jeffrey': 5
    }

    location_names = {
        0: 'Nob Hill',
        1: 'Richmond District',
        2: 'Financial District',
        3: 'North Beach',
        4: 'The Castro',
        5: 'Golden Gate Park'
    }

    travel_matrix = [
        [0, 14, 9, 8, 17, 17],
        [17, 0, 22, 17, 16, 9],
        [8, 21, 0, 7, 23, 23],
        [7, 18, 8, 0, 22, 22],
        [16, 16, 20, 20, 0, 11],
        [20, 7, 26, 24, 13, 0]
    ]

    # Create optimizer
    opt = Optimize()
    
    # Create variables for each friend
    meets = {}
    starts = {}
    ends = {}
    for friend in ['Emily', 'Margaret', 'Ronald', 'Deborah', 'Jeffrey']:
        meets[friend] = Bool(f'meet_{friend}')
        starts[friend] = Int(f'start_{friend}')
        ends[friend] = Int(f'end_{friend}')

    # Add constraints for each friend
    for friend in meets:
        loc_idx = location_indices[friend]
        window_start, window_end = windows[friend]
        min_dur = min_durations[friend]
        
        # If meeting happens, constrain time window and duration
        opt.add(Implies(meets[friend], starts[friend] >= window_start))
        opt.add(Implies(meets[friend], ends[friend] <= window_end))
        opt.add(Implies(meets[friend], ends[friend] - starts[friend] >= min_dur))
        
        # Travel time from starting point (Nob Hill)
        travel_time_from_start = travel_matrix[0][loc_idx]
        opt.add(Implies(meets[friend], starts[friend] >= base_time + travel_time_from_start))

    # Add constraints for travel times between meetings
    friends = list(meets.keys())
    for i in range(len(friends)):
        for j in range(i + 1, len(friends)):
            friend_i = friends[i]
            friend_j = friends[j]
            loc_i = location_indices[friend_i]
            loc_j = location_indices[friend_j]
            
            travel_ij = travel_matrix[loc_i][loc_j]
            travel_ji = travel_matrix[loc_j][loc_i]
            
            # Either meeting i is before j or j is before i
            constraint = Implies(And(meets[friend_i], meets[friend_j]),
                                Or(ends[friend_i] + travel_ij <= starts[friend_j],
                                   ends[friend_j] + travel_ji <= starts[friend_i]))
            opt.add(constraint)

    # Maximize number of meetings
    opt.maximize(Sum([If(meets[friend], 1, 0) for friend in meets]))
    
    # Check and get model
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        
        # Collect all meetings that happened
        meetings = []
        for friend in meets:
            if is_true(model[meets[friend]]):
                start_val = model[starts[friend]].as_long()
                end_val = model[ends[friend]].as_long()
                location = location_names[location_indices[friend]]
                meetings.append({
                    'friend': friend,
                    'start': start_val,
                    'end': end_val,
                    'location': location
                })
        
        # Sort meetings by start time
        meetings.sort(key=lambda x: x['start'])
        
        # Format itinerary
        for meeting in meetings:
            start_hour = meeting['start'] // 60
            start_minute = meeting['start'] % 60
            end_hour = meeting['end'] // 60
            end_minute = meeting['end'] % 60
            
            itinerary.append({
                'action': 'meet',
                'location': meeting['location'],
                'person': meeting['friend'],
                'start_time': f'{start_hour}:{start_minute:02d}',
                'end_time': f'{end_hour}:{end_minute:02d}'
            })
        
        # Output JSON
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()