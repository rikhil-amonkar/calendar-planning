from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define the locations and their travel times (in minutes)
    locations = {
        'Financial District': 0,
        'Russian Hill': 1,
        'Sunset District': 2,
        'North Beach': 3,
        'The Castro': 4,
        'Golden Gate Park': 5
    }

    # Travel times matrix: from_location x to_location -> minutes
    travel_times = [
        [0, 10, 31, 7, 23, 23],    # Financial District
        [11, 0, 23, 5, 21, 21],     # Russian Hill
        [30, 24, 0, 29, 17, 11],    # Sunset District
        [8, 4, 27, 0, 22, 22],      # North Beach
        [20, 18, 17, 20, 0, 11],    # The Castro
        [26, 19, 10, 24, 13, 0]     # Golden Gate Park
    ]

    # Friends' data: name, location, available start and end times, min duration
    friends = [
        {'name': 'Ronald', 'location': 'Russian Hill', 'start': (13, 45), 'end': (17, 15), 'min_duration': 105},
        {'name': 'Patricia', 'location': 'Sunset District', 'start': (9, 15), 'end': (22, 0), 'min_duration': 60},
        {'name': 'Laura', 'location': 'North Beach', 'start': (12, 30), 'end': (12, 45), 'min_duration': 15},
        {'name': 'Emily', 'location': 'The Castro', 'start': (16, 15), 'end': (18, 30), 'min_duration': 60},
        {'name': 'Mary', 'location': 'Golden Gate Park', 'start': (15, 0), 'end': (16, 30), 'min_duration': 60}
    ]

    # Convert friend's availability to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(hour, minute):
        return hour * 60 + minute - 540  # 9:00 AM is 540 minutes

    # Convert minutes back to time string
    def minutes_to_time(m):
        total_minutes = 540 + m
        h = total_minutes // 60
        mi = total_minutes % 60
        return f"{h:02d}:{mi:02d}"

    # Create variables for each friend's meeting start and end times (in minutes since 9:00 AM)
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

    # Constraints to ensure no overlapping meetings and travel time between meetings
    for i in range(len(friend_vars)):
        for j in range(i + 1, len(friend_vars)):
            f1 = friend_vars[i]
            f2 = friend_vars[j]
            loc1 = locations[f1['location']]
            loc2 = locations[f2['location']]
            travel = travel_times[loc1][loc2]
            # Scenario 1: f1 before f2
            c1 = And(f1['end'] + travel <= f2['start'])
            # Scenario 2: f2 before f1
            c2 = And(f2['end'] + travel_times[loc2][loc1] <= f1['start'])
            s.add(Or(c1, c2))

    # Also, the first meeting must start after arrival time (9:00 AM, 0 minutes)
    # But the friends' start times are already constrained to their availability.

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend in friend_vars:
            start_val = model[friend['start']].as_long()
            end_val = model[friend['end']].as_long()
            itinerary.append({
                "action": "meet",
                "person": friend['name'],
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))