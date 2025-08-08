from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define locations and travel times
    locations = {
        'Fisherman\'s Wharf': 0,
        'The Castro': 1,
        'Golden Gate Park': 2,
        'Embarcadero': 3,
        'Russian Hill': 4,
        'Nob Hill': 5,
        'Alamo Square': 6,
        'North Beach': 7
    }

    travel_times = [
        [0, 26, 25, 8, 7, 11, 20, 6],
        [24, 0, 11, 22, 18, 16, 8, 20],
        [24, 13, 0, 25, 19, 20, 10, 24],
        [6, 25, 25, 0, 8, 10, 19, 5],
        [7, 21, 21, 8, 0, 5, 15, 5],
        [11, 17, 17, 9, 5, 0, 11, 8],
        [19, 8, 9, 17, 13, 11, 0, 15],
        [5, 22, 22, 6, 4, 7, 16, 0]
    ]

    # Friends data
    friends = [
        {'name': 'Laura', 'location': 'The Castro', 'start': (19, 45), 'end': (21, 30), 'duration': 105},
        {'name': 'Daniel', 'location': 'Golden Gate Park', 'start': (21, 15), 'end': (21, 45), 'duration': 15},
        {'name': 'William', 'location': 'Embarcadero', 'start': (7, 0), 'end': (9, 0), 'duration': 90},
        {'name': 'Karen', 'location': 'Russian Hill', 'start': (14, 30), 'end': (19, 45), 'duration': 30},
        {'name': 'Stephanie', 'location': 'Nob Hill', 'start': (7, 30), 'end': (9, 30), 'duration': 45},
        {'name': 'Joseph', 'location': 'Alamo Square', 'start': (11, 30), 'end': (12, 45), 'duration': 15},
        {'name': 'Kimberly', 'location': 'North Beach', 'start': (15, 45), 'end': (19, 15), 'duration': 30}
    ]

    # Helper functions
    def time_to_minutes(time_tuple):
        return time_tuple[0] * 60 + time_tuple[1]

    def minutes_to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"

    # Create variables
    meeting_vars = []
    for friend in friends:
        start_var = Int(f"start_{friend['name']}")
        end_var = Int(f"end_{friend['name']}")
        meeting_vars.append((friend, start_var, end_var))

    # Add basic constraints
    for friend, start, end in meeting_vars:
        s.add(start >= time_to_minutes(friend['start']))
        s.add(end <= time_to_minutes(friend['end']))
        s.add(end - start >= friend['duration'])

    # Starting point
    current_time = 540  # 9:00 AM
    current_loc = locations['Fisherman\'s Wharf']

    # Create meeting sequence
    sequence = []
    for i, (friend, start, end) in enumerate(meeting_vars):
        loc = locations[friend['location']]
        travel_time = travel_times[current_loc][loc]
        s.add(start >= current_time + travel_time)
        sequence.append((start, end, loc))
        current_time = end
        current_loc = loc

    # No overlapping meetings
    for i in range(len(meeting_vars)):
        for j in range(i+1, len(meeting_vars)):
            _, end1, loc1 = sequence[i]
            start2, _, loc2 = sequence[j]
            travel_time = travel_times[loc1][loc2]
            s.add(end1 + travel_time <= start2)

    # Special constraints for critical meetings
    for friend, start, end in meeting_vars:
        if friend['name'] == 'Laura':
            s.add(start == time_to_minutes((19, 45)))
        if friend['name'] == 'Daniel':
            s.add(start == time_to_minutes((21, 15)))

    # Solve
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend, start_var, end_var in meeting_vars:
            start_val = model[start_var].as_long()
            end_val = model[end_var].as_long()
            itinerary.append({
                "action": "meet",
                "person": friend['name'],
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling()
print("SOLUTION:")
print(json.dumps(solution, indent=2))