from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define friends and their details
    friends = {
        'Paul': {'location': 'Nob Hill', 'available_start': 16.25, 'available_end': 21.25, 'duration': 1.0},
        'Carol': {'location': 'Union Square', 'available_start': 18.0, 'available_end': 20.25, 'duration': 2.0},
        'Patricia': {'location': 'Chinatown', 'available_start': 20.0, 'available_end': 21.5, 'duration': 1.25},
        'Karen': {'location': 'The Castro', 'available_start': 17.0, 'available_end': 19.0, 'duration': 0.75},
        'Nancy': {'location': 'Presidio', 'available_start': 11.75, 'available_end': 22.0, 'duration': 0.5},
        'Jeffrey': {'location': 'Pacific Heights', 'available_start': 20.0, 'available_end': 20.75, 'duration': 0.75},
        'Matthew': {'location': 'Russian Hill', 'available_start': 15.75, 'available_end': 21.75, 'duration': 1.25}
    }

    # Define travel times (from_location -> to_location: hours)
    travel_times = {
        'Bayview': {
            'Nob Hill': 20/60, 'Union Square': 17/60, 'Chinatown': 18/60,
            'The Castro': 20/60, 'Presidio': 31/60, 'Pacific Heights': 23/60,
            'Russian Hill': 23/60
        },
        'Nob Hill': {
            'Bayview': 19/60, 'Union Square': 7/60, 'Chinatown': 6/60,
            'The Castro': 17/60, 'Presidio': 17/60, 'Pacific Heights': 8/60,
            'Russian Hill': 5/60
        },
        'Union Square': {
            'Bayview': 15/60, 'Nob Hill': 9/60, 'Chinatown': 7/60,
            'The Castro': 19/60, 'Presidio': 24/60, 'Pacific Heights': 15/60,
            'Russian Hill': 13/60
        },
        'Chinatown': {
            'Bayview': 22/60, 'Nob Hill': 8/60, 'Union Square': 7/60,
            'The Castro': 22/60, 'Presidio': 19/60, 'Pacific Heights': 10/60,
            'Russian Hill': 7/60
        },
        'The Castro': {
            'Bayview': 19/60, 'Nob Hill': 16/60, 'Union Square': 19/60,
            'Chinatown': 20/60, 'Presidio': 20/60, 'Pacific Heights': 16/60,
            'Russian Hill': 18/60
        },
        'Presidio': {
            'Bayview': 31/60, 'Nob Hill': 18/60, 'Union Square': 22/60,
            'Chinatown': 21/60, 'The Castro': 21/60, 'Pacific Heights': 11/60,
            'Russian Hill': 14/60
        },
        'Pacific Heights': {
            'Bayview': 22/60, 'Nob Hill': 8/60, 'Union Square': 12/60,
            'Chinatown': 11/60, 'The Castro': 16/60, 'Presidio': 11/60,
            'Russian Hill': 7/60
        },
        'Russian Hill': {
            'Bayview': 23/60, 'Nob Hill': 5/60, 'Union Square': 11/60,
            'Chinatown': 9/60, 'The Castro': 21/60, 'Presidio': 14/60,
            'Pacific Heights': 7/60
        }
    }

    # Create variables for each friend's meeting start and end times
    start_vars = {friend: Real(f'start_{friend}') for friend in friends}
    end_vars = {friend: Real(f'end_{friend}') for friend in friends}

    # Current location starts at Bayview at 9:00 AM (9.0)
    current_time = Real('current_time')
    s.add(current_time == 9.0)
    current_location = 'Bayview'

    # Constraints for each friend
    for friend in friends:
        details = friends[friend]
        s.add(start_vars[friend] >= details['available_start'])
        s.add(end_vars[friend] <= details['available_end'])
        s.add(end_vars[friend] == start_vars[friend] + details['duration'])
        
        # Travel time from current location to friend's location
        travel_time = travel_times[current_location][details['location']]
        s.add(start_vars[friend] >= current_time + travel_time)
        
        # Update current location and time after meeting this friend
        current_time = end_vars[friend]
        current_location = details['location']

    # Additional constraints to ensure meetings don't overlap
    # We'll use the order of friends in the dictionary as a possible sequence
    friend_list = list(friends.keys())
    for i in range(len(friend_list)-1):
        friend1 = friend_list[i]
        friend2 = friend_list[i+1]
        s.add(start_vars[friend2] >= end_vars[friend1] + travel_times[friends[friend1]['location']][friends[friend2]['location']])

    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        schedule = []
        for friend in friends:
            start = float(model.eval(start_vars[friend]).as_decimal(3))
            end = float(model.eval(end_vars[friend]).as_decimal(3))
            schedule.append((friend, start, end))
        
        # Sort schedule by start time
        schedule.sort(key=lambda x: x[1])
        
        # Print the schedule
        print("SOLUTION:")
        for meeting in schedule:
            friend, start, end = meeting
            start_hour = int(start)
            start_min = int((start - start_hour) * 60)
            end_hour = int(end)
            end_min = int((end - end_hour) * 60)
            print(f"Meet {friend} at {friends[friend]['location']} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}")
    else:
        print("No feasible schedule found.")

solve_scheduling()