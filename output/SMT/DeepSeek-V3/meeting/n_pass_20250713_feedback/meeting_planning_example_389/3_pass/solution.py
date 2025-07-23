from z3 import *
from itertools import combinations, permutations

def solve_scheduling():
    # Define all friends and their constraints
    friends = {
        'Sarah': {
            'location': 'Fisherman\'s Wharf',
            'window_start': 345,  # 2:45 PM in minutes since 9:00 AM
            'window_end': 510,    # 5:30 PM
            'min_duration': 105,
            'travel_from_prev': {
                'Haight-Ashbury': 23,
                'Richmond District': 18,
                'Mission District': 22,
                'Bayview': 26
            }
        },
        'Mary': {
            'location': 'Richmond District',
            'window_start': 240,  # 1:00 PM
            'window_end': 615,    # 7:15 PM
            'min_duration': 75,
            'travel_from_prev': {
                'Haight-Ashbury': 10,
                'Fisherman\'s Wharf': 18,
                'Mission District': 20,
                'Bayview': 26
            }
        },
        'Helen': {
            'location': 'Mission District',
            'window_start': 765,  # 9:45 PM
            'window_end': 810,    # 10:30 PM
            'min_duration': 30,
            'travel_from_prev': {
                'Haight-Ashbury': 11,
                'Fisherman\'s Wharf': 22,
                'Richmond District': 20,
                'Bayview': 15
            }
        },
        'Thomas': {
            'location': 'Bayview',
            'window_start': 375,  # 3:15 PM
            'window_end': 585,    # 6:45 PM
            'min_duration': 120,
            'travel_from_prev': {
                'Haight-Ashbury': 18,
                'Fisherman\'s Wharf': 25,
                'Richmond District': 25,
                'Mission District': 13
            }
        }
    }

    # Generate all possible combinations of 3 friends
    friend_combinations = combinations(friends.keys(), 3)

    for combo in friend_combinations:
        # Initialize solver
        s = Solver()

        # Create variables for start and end times of each friend in the combination
        time_vars = {}
        for friend in combo:
            time_vars[friend] = {
                'start': Int(f'{friend}_start'),
                'end': Int(f'{friend}_end')
            }

        # Add constraints for each friend's meeting window and duration
        for friend in combo:
            friend_info = friends[friend]
            s.add(time_vars[friend]['start'] >= friend_info['window_start'])
            s.add(time_vars[friend]['end'] <= friend_info['window_end'])
            s.add(time_vars[friend]['end'] - time_vars[friend]['start'] >= friend_info['min_duration'])

        # Define the order of meetings and add travel time constraints
        # We need to consider all possible orders of the 3 friends
        for order in permutations(combo):
            # Reset the solver for each order
            s = Solver()

            # Re-add the meeting constraints
            for friend in combo:
                friend_info = friends[friend]
                s.add(time_vars[friend]['start'] >= friend_info['window_start'])
                s.add(time_vars[friend]['end'] <= friend_info['window_end'])
                s.add(time_vars[friend]['end'] - time_vars[friend]['start'] >= friend_info['min_duration'])

            # Add travel time constraints based on the order
            prev_location = 'Haight-Ashbury'
            prev_end = 0  # Start at 9:00 AM (0 minutes since 9:00 AM)
            for i, friend in enumerate(order):
                friend_info = friends[friend]
                travel_time = friend_info['travel_from_prev'][prev_location]
                s.add(time_vars[friend]['start'] >= prev_end + travel_time)
                prev_end = time_vars[friend]['end']
                prev_location = friend_info['location']

            # Check if this order is feasible
            if s.check() == sat:
                m = s.model()
                # Verify Helen's meeting time is within her window
                if 'Helen' in combo:
                    helen_start = m[time_vars['Helen']['start']].as_long()
                    helen_end = m[time_vars['Helen']['end']].as_long()
                    if helen_start >= 765 and helen_end <= 810:
                        print(f"Feasible schedule found for friends: {', '.join(order)}")
                        for friend in order:
                            start = m[time_vars[friend]['start']].as_long()
                            end = m[time_vars[friend]['end']].as_long()
                            print(f"Meet {friend} from {start} to {end} minutes since 9:00 AM.")
                        return  # Exit after finding the first feasible schedule
                else:
                    print(f"Feasible schedule found for friends: {', '.join(order)}")
                    for friend in order:
                        start = m[time_vars[friend]['start']].as_long()
                        end = m[time_vars[friend]['end']].as_long()
                        print(f"Meet {friend} from {start} to {end} minutes since 9:00 AM.")
                    return  # Exit after finding the first feasible schedule

    print("No feasible schedule found for any combination of three friends.")

solve_scheduling()