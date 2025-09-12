import z3
import json

# Define location names
location_names = [
    'Chinatown',
    'Embarcadero',
    'Pacific Heights',
    'Russian Hill',
    'Haight-Ashbury',
    'Golden Gate Park',
    "Fisherman's Wharf",
    'Sunset District',
    'The Castro'
]

# Define friends data with corrected earliest and latest times
friends = [
    {
        'name': 'Richard',
        'location': 1,
        'location_name': location_names[1],
        'earliest': 15 * 60 + 15,  # 3:15 PM
        'latest': 18 * 60 + 45,    # 6:45 PM
        'min_duration': 90
    },
    {
        'name': 'Mark',
        'location': 2,
        'location_name': location_names[2],
        'earliest': 15 * 60,        # 3:00 PM
        'latest': 17 * 60,          # 5:00 PM
        'min_duration': 45
    },
    {
        'name': 'Matthew',
        'location': 3,
        'location_name': location_names[3],
        'earliest': 17 * 60 + 30,   # 5:30 PM
        'latest': 21 * 60,          # 9:00 PM
        'min_duration': 90
    },
    {
        'name': 'Rebecca',
        'location': 4,
        'location_name': location_names[4],
        'earliest': 14 * 60 + 45,   # 2:45 PM
        'latest': 18 * 60,          # 6:00 PM
        'min_duration': 60
    },
    {
        'name': 'Melissa',
        'location': 5,
        'location_name': location_names[5],
        'earliest': 13 * 60 + 45,   # 1:45 PM
        'latest': 17 * 60 + 30,     # 5:30 PM
        'min_duration': 90
    },
    {
        'name': 'Margaret',
        'location': 6,
        'location_name': location_names[6],
        'earliest': 14 * 60 + 45,   # 2:45 PM
        'latest': 20 * 60 + 15,     # 8:15 PM
        'min_duration': 15
    },
    {
        'name': 'Emily',
        'location': 7,
        'location_name': location_names[7],
        'earliest': 15 * 60 + 45,   # 3:45 PM
        'latest': 17 * 60,          # 5:00 PM
        'min_duration': 45
    },
    {
        'name': 'George',
        'location': 8,
        'location_name': location_names[8],
        'earliest': 14 * 60,        # 2:00 PM
        'latest': 16 * 60 + 15,     # 4:15 PM
        'min_duration': 75
    }
]

# Define travel_time matrix
travel_time = [
    [0, 5, 10, 7, 19, 23, 8, 29, 22],
    [7, 0, 11, 8, 21, 25, 6, 30, 25],
    [11, 10, 0, 7, 11, 15, 13, 21, 16],
    [9, 8, 7, 0, 17, 21, 7, 23, 21],
    [19, 20, 12, 17, 0, 7, 23, 15, 6],
    [23, 25, 16, 19, 7, 0, 24, 10, 13],
    [12, 8, 12, 7, 22, 25, 0, 27, 24],
    [30, 30, 21, 24, 15, 11, 29, 0, 17],
    [22, 22, 16, 18, 6, 11, 24, 17, 0]
]

# Now, try k from 8 down to 1
for k in range(8, 0, -1):
    solver = z3.Solver()

    # Create variables
    friend_ids = [z3.Int(f'friend_{i}') for i in range(k)]
    start_times = [z3.Int(f'start_{i}') for i in range(k)]
    end_times = [z3.Int(f'end_{i}') for i in range(k)]
    locations = [z3.Int(f'location_{i}') for i in range(k)]

    # Add constraints for location based on friend_id
    for i in range(k):
        conds = []
        for fid in range(8):
            conds.append(z3.And(friend_ids[i] == fid, locations[i] == friends[fid]['location']))
        solver.add(z3.Or(conds))

    # Add travel_time function
    travel_time_func = z3.Function('travel_time_func', z3.IntSort(), z3.IntSort(), z3.IntSort())
    for loc_prev in range(9):
        for loc_current in range(9):
            solver.add(travel_time_func(loc_prev, loc_current) == travel_time[loc_prev][loc_current])

    # Add time constraints for each meeting
    for i in range(k):
        # Build earliest_expr
        earliest_expr = friends[0]['earliest']
        for fid in range(1, 8):
            earliest_expr = z3.If(friend_ids[i] == fid, friends[fid]['earliest'], earliest_expr)
        solver.add(start_times[i] >= earliest_expr)

        # Build latest_expr
        latest_expr = friends[0]['latest']
        for fid in range(1, 8):
            latest_expr = z3.If(friend_ids[i] == fid, friends[fid]['latest'], latest_expr)
        solver.add(end_times[i] <= latest_expr)

        # Build min_duration_expr
        min_duration_expr = friends[0]['min_duration']
        for fid in range(1, 8):
            min_duration_expr = z3.If(friend_ids[i] == fid, friends[fid]['min_duration'], min_duration_expr)
        solver.add(end_times[i] - start_times[i] >= min_duration_expr)

    # Add travel time constraints
    for i in range(k):
        if i == 0:
            loc_prev = 0  # Start from Chinatown
            loc_current = locations[i]
            solver.add(start_times[i] >= 540 + travel_time_func(loc_prev, loc_current))
        else:
            loc_prev = locations[i-1]
            loc_current = locations[i]
            solver.add(start_times[i] >= end_times[i-1] + travel_time_func(loc_prev, loc_current))

    # Add uniqueness constraints for friend_ids
    for i in range(k):
        for j in range(i+1, k):
            solver.add(friend_ids[i] != friend_ids[j])

    # Check if the constraints are satisfiable
    if solver.check() == z3.sat:
        model = solver.model()
        # Extract the solution
        itinerary = []
        for i in range(k):
            fid = model.evaluate(friend_ids[i]).as_long()
            start = model.evaluate(start_times[i]).as_long()
            end = model.evaluate(end_times[i]).as_long()
            friend = friends[fid]
            # Convert start and end to H:MM format
            def to_time(mins):
                hours = mins // 60
                minutes = mins % 60
                return f"{hours % 24}:{minutes:02d}"
            itinerary.append({
                "action": "meet",
                "location": friend['location_name'],
                "person": friend['name'],
                "start_time": to_time(start),
                "end_time": to_time(end)
            })
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
        exit()

# If no solution found for any k
print(json.dumps({"itinerary": []}))