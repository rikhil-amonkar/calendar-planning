from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the locations and their travel times
    locations = {
        'Financial District': 0,
        'Golden Gate Park': 1,
        'Chinatown': 2,
        'Union Square': 3,
        'Fisherman\'s Wharf': 4,
        'Pacific Heights': 5,
        'North Beach': 6
    }

    # Travel times matrix (from_location, to_location) -> minutes
    travel_times = {
        (0, 1): 23, (0, 2): 5, (0, 3): 9, (0, 4): 10, (0, 5): 13, (0, 6): 7,
        (1, 0): 26, (1, 2): 23, (1, 3): 22, (1, 4): 24, (1, 5): 16, (1, 6): 24,
        (2, 0): 5, (2, 1): 23, (2, 3): 7, (2, 4): 8, (2, 5): 10, (2, 6): 3,
        (3, 0): 9, (3, 1): 22, (3, 2): 7, (3, 4): 15, (3, 5): 15, (3, 6): 10,
        (4, 0): 11, (4, 1): 25, (4, 2): 12, (4, 3): 13, (4, 5): 12, (4, 6): 6,
        (5, 0): 13, (5, 1): 15, (5, 2): 11, (5, 3): 12, (5, 4): 13, (5, 6): 9,
        (6, 0): 8, (6, 1): 22, (6, 2): 6, (6, 3): 7, (6, 4): 5, (6, 5): 8
    }

    # Friends' availability and constraints
    friends = {
        'Stephanie': {'location': 'Golden Gate Park', 'start': 11*60, 'end': 15*60, 'min_duration': 105},
        'Karen': {'location': 'Chinatown', 'start': 13*60 + 45, 'end': 16*60 + 30, 'min_duration': 15},
        'Brian': {'location': 'Union Square', 'start': 15*60, 'end': 17*60 + 15, 'min_duration': 30},
        'Rebecca': {'location': 'Fisherman\'s Wharf', 'start': 8*60, 'end': 11*60 + 15, 'min_duration': 30},
        'Joseph': {'location': 'Pacific Heights', 'start': 8*60 + 15, 'end': 9*60 + 30, 'min_duration': 60},
        'Steven': {'location': 'North Beach', 'start': 14*60 + 30, 'end': 20*60 + 45, 'min_duration': 120}
    }

    # Current location starts at Financial District at 9:00 AM (540 minutes)
    current_time = 9 * 60
    current_location = locations['Financial District']

    # Variables for each meeting
    meetings = {}
    for name in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        meetings[name] = {'start': start, 'end': end, 'location': locations[friends[name]['location']]}

    # Constraints for each meeting
    for name in friends:
        friend = friends[name]
        meeting = meetings[name]
        s.add(meeting['start'] >= friend['start'])
        s.add(meeting['end'] <= friend['end'])
        s.add(meeting['end'] - meeting['start'] >= friend['min_duration'])

    # Define the order of meetings using permutation variables
    meeting_names = list(friends.keys())
    n = len(meeting_names)
    order = [Int(f'order_{i}') for i in range(n)]

    # Each order variable must be between 0 and n-1
    for i in range(n):
        s.add(order[i] >= 0, order[i] < n)

    # All order variables must be distinct
    s.add(Distinct(order))

    # Variables to track the current time and location after each meeting
    times = [Int(f'time_{i}') for i in range(n + 1)]
    locs = [Int(f'loc_{i}') for i in range(n + 1)]

    # Initial conditions
    s.add(times[0] == current_time)
    s.add(locs[0] == current_location)

    # Constraints for the order of meetings
    for i in range(n):
        # Get the name of the friend at position i in the order
        name = meeting_names[order[i]]
        meeting = meetings[name]
        # The start time of the meeting must be after the previous time plus travel time
        s.add(meeting['start'] >= times[i] + travel_times[(locs[i], meeting['location'])])
        # The next time is the end of the meeting
        s.add(times[i + 1] == meeting['end'])
        # The next location is the meeting's location
        s.add(locs[i + 1] == meeting['location'])

    # Check if the solution is satisfiable
    if s.check() == sat:
        m = s.model()
        # Get the order of meetings
        meeting_order = sorted([(m[order[i]].as_long(), meeting_names[i]) for i in range(n)], key=lambda x: x[0])
        itinerary = []
        for idx, name in meeting_order:
            start = m[meetings[name]['start']].as_long()
            end = m[meetings[name]['end']].as_long()
            start_time = f"{start // 60:02d}:{start % 60:02d}"
            end_time = f"{end // 60:02d}:{end % 60:02d}"
            itinerary.append({"action": "meet", "person": name, "start_time": start_time, "end_time": end_time})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid schedule found"}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))