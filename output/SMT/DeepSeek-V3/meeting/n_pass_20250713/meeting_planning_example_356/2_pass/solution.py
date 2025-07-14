from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the locations
    locations = ['Bayview', 'North Beach', 'Presidio', 'Haight-Ashbury', 'Union Square']
    location_indices = {loc: idx for idx, loc in enumerate(locations)}

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 21, 31, 19, 17],    # Bayview to others
        [22, 0, 17, 18, 7],      # North Beach to others
        [31, 18, 0, 15, 22],     # Presidio to others
        [18, 19, 15, 0, 17],     # Haight-Ashbury to others
        [15, 10, 24, 18, 0]      # Union Square to others
    ]

    # Friend constraints
    friends = {
        'Barbara': {'location': 'North Beach', 'start': 13*60 + 45, 'end': 20*60 + 15, 'min_duration': 60},
        'Margaret': {'location': 'Presidio', 'start': 10*60 + 15, 'end': 15*60 + 15, 'min_duration': 30},
        'Kevin': {'location': 'Haight-Ashbury', 'start': 20*60 + 0, 'end': 20*60 + 45, 'min_duration': 30},
        'Kimberly': {'location': 'Union Square', 'start': 7*60 + 45, 'end': 16*60 + 45, 'min_duration': 30}
    }

    # Variables for each friend: start and end times of the meeting
    meeting_start = {name: Int(f'start_{name}') for name in friends}
    meeting_end = {name: Int(f'end_{name}') for name in friends}

    # Initial constraints: arrival at Bayview at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = 'Bayview'

    # Constraints for each friend
    for name in friends:
        info = friends[name]
        loc = info['location']
        travel_time = travel_times[location_indices[current_location]][location_indices[loc]]

        # Meeting must fit within friend's availability and our schedule
        s.add(meeting_start[name] >= info['start'])
        s.add(meeting_end[name] <= info['end'])
        s.add(meeting_end[name] - meeting_start[name] >= info['min_duration'])
        s.add(meeting_start[name] >= current_time + travel_time)

    # Ensure no overlapping meetings and account for travel times
    # We need to define the order of meetings since all four must be scheduled
    # Let's assume an arbitrary order and let Z3 find a feasible permutation
    # For simplicity, we'll use a list of friends and enforce constraints between consecutive meetings
    friend_order = list(friends.keys())
    for i in range(len(friend_order) - 1):
        name1 = friend_order[i]
        name2 = friend_order[i + 1]
        loc1 = friends[name1]['location']
        loc2 = friends[name2]['location']
        travel = travel_times[location_indices[loc1]][location_indices[loc2]]
        s.add(meeting_end[name1] + travel <= meeting_start[name2])

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        # Print the schedule
        print("SOLUTION:")
        for name in friends:
            start = m.evaluate(meeting_start[name]).as_long()
            end = m.evaluate(meeting_end[name]).as_long()
            print(f"Meet {name} at {friends[name]['location']} from {start//60}:{start%60:02d} to {end//60}:{end%60:02d}")
    else:
        print("No solution found")

solve_scheduling()