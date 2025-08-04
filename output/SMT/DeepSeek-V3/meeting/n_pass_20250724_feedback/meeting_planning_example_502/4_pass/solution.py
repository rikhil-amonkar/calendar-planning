from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the locations and their indices
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
    travel_times = [
        [0, 23, 5, 9, 10, 13, 7],    # Financial District
        [26, 0, 23, 22, 24, 16, 24], # Golden Gate Park
        [5, 23, 0, 7, 8, 10, 3],     # Chinatown
        [9, 22, 7, 0, 15, 15, 10],   # Union Square
        [11, 25, 12, 13, 0, 12, 6],  # Fisherman's Wharf
        [13, 15, 11, 12, 13, 0, 9],  # Pacific Heights
        [8, 22, 6, 7, 5, 8, 0]       # North Beach
    ]

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
        meetings[name] = {
            'start': start,
            'end': end,
            'location': locations[friends[name]['location']]
        }

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

    # Function to get travel time between two locations
    def get_travel_time(from_loc, to_loc):
        # Create a case for each possible from_loc
        cases = []
        for i in range(len(travel_times)):
            cases.append((from_loc == i, travel_times[i][to_loc]))
        return If(cases[0][0], cases[0][1],
                If(cases[1][0], cases[1][1],
                If(cases[2][0], cases[2][1],
                If(cases[3][0], cases[3][1],
                If(cases[4][0], cases[4][1],
                If(cases[5][0], cases[5][1],
                cases[6][1]))))))

    # Constraints for the order of meetings
    for i in range(n):
        # The start time of the meeting must be after the previous time plus travel time
        # We need to find which meeting is at position i
        # Create a condition for each possible meeting at position i
        for j in range(n):
            name = meeting_names[j]
            meeting = meetings[name]
            travel_time = get_travel_time(locs[i], meeting['location'])
            s.add(Implies(order[i] == j,
                          And(meeting['start'] >= times[i] + travel_time,
                              times[i + 1] == meeting['end'],
                              locs[i + 1] == meeting['location'])))

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