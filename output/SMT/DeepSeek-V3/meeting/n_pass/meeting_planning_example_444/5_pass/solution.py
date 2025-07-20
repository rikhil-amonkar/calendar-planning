from z3 import *
import json

def solve_scheduling():
    # Initialize solver with optimization
    s = Optimize()
    s.set("timeout", 60000)  # Give ample time to find solution

    # Define locations and travel times (in minutes)
    locations = {
        'Financial District': 0,
        'Russian Hill': 1,
        'Sunset District': 2,
        'North Beach': 3,
        'The Castro': 4,
        'Golden Gate Park': 5
    }

    # Travel times matrix
    travel_times = [
        [0, 10, 31, 7, 23, 23],
        [11, 0, 23, 5, 21, 21],
        [30, 24, 0, 29, 17, 11],
        [8, 4, 27, 0, 22, 22],
        [20, 18, 17, 20, 0, 11],
        [26, 19, 10, 24, 13, 0]
    ]

    # Friends' data
    friends = [
        {'name': 'Ronald', 'location': 'Russian Hill', 'start': (13, 45), 'end': (17, 15), 'min_duration': 105},
        {'name': 'Patricia', 'location': 'Sunset District', 'start': (9, 15), 'end': (22, 0), 'min_duration': 60},
        {'name': 'Laura', 'location': 'North Beach', 'start': (12, 30), 'end': (12, 45), 'min_duration': 15},
        {'name': 'Emily', 'location': 'The Castro', 'start': (16, 15), 'end': (18, 30), 'min_duration': 60},
        {'name': 'Mary', 'location': 'Golden Gate Park', 'start': (15, 0), 'end': (16, 30), 'min_duration': 60}
    ]

    # Time conversion functions
    def time_to_minutes(hour, minute):
        return hour * 60 + minute - 540  # 9:00 AM is 540 minutes

    def minutes_to_time(m):
        total_minutes = 540 + m
        h = total_minutes // 60
        mi = total_minutes % 60
        return f"{h:02d}:{mi:02d}"

    # Create variables
    friend_vars = []
    for friend in friends:
        start_min = time_to_minutes(friend['start'][0], friend['start'][1])
        end_min = time_to_minutes(friend['end'][0], friend['end'][1])
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        s.add(start >= start_min)
        s.add(end <= end_min)
        s.add(end - start >= friend['min_duration'])
        friend_vars.append({
            'name': friend['name'],
            'location': friend['location'],
            'start': start,
            'end': end
        })

    # Create sequence variables
    n = len(friend_vars)
    seq = [Int(f"seq_{i}") for i in range(n)]
    s.add(Distinct(seq))
    s.add([And(seq[i] >= 0, seq[i] < n) for i in range(n)])

    # Travel time constraints
    current_location = locations['Financial District']
    current_time = 0  # 9:00 AM
    travel_cumulative = 0

    for i in range(n):
        # Get the friend at position i in sequence
        f = friend_vars[seq[i]]
        loc = locations[f['location']]
        
        # Travel time from current location to friend's location
        travel = travel_times[current_location][loc]
        s.add(f['start'] >= current_time + travel)
        
        # Update current location and time
        current_location = loc
        current_time = f['end']
        travel_cumulative += travel

    # Try to maximize total meeting time
    total_meeting_time = sum([f['end'] - f['start'] for f in friend_vars])
    s.maximize(total_meeting_time)

    if s.check() == sat:
        model = s.model()
        # Get the sequence order
        seq_order = sorted([(model[seq[i]].as_long(), i) for i in range(n)])
        ordered_friends = [friend_vars[i] for _, i in seq_order]
        
        itinerary = []
        for friend in ordered_friends:
            start_val = model[friend['start']].as_long()
            end_val = model[friend['end']].as_long()
            itinerary.append({
                "action": "meet",
                "person": friend['name'],
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))