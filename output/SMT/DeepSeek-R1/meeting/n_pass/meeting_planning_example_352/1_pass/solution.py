from z3 import *

def main():
    # Initialize the optimization solver
    s = Optimize()
    
    # Boolean variables for meeting each friend
    meet_S = Bool('meet_S')
    meet_J = Bool('meet_J')
    meet_N = Bool('meet_N')
    meet_K = Bool('meet_K')
    
    # Start time variables for each friend (in minutes from 9:00 AM)
    start_S = Real('start_S')
    start_J = Real('start_J')
    start_N = Real('start_N')
    start_K = Real('start_K')
    
    # Travel times from Union Square to each location
    travel_from_U = {
        'Chinatown': 7,          # Sandra
        'Haight-Ashbury': 18,     # Joseph
        'Marina District': 18,    # Nancy
        'Nob Hill': 9             # Karen
    }
    
    # Travel times between locations (from -> to)
    travel_times = {
        'Chinatown': {
            'Haight-Ashbury': 19,
            'Marina District': 12,
            'Nob Hill': 8
        },
        'Haight-Ashbury': {
            'Chinatown': 19,
            'Marina District': 17,
            'Nob Hill': 15
        },
        'Marina District': {
            'Chinatown': 16,
            'Haight-Ashbury': 16,
            'Nob Hill': 12
        },
        'Nob Hill': {
            'Chinatown': 6,
            'Haight-Ashbury': 13,
            'Marina District': 11
        }
    }
    
    # Friend details: location, availability start, availability end, duration
    friends = {
        'S': {'loc': 'Chinatown', 'avail_start': 0, 'avail_end': 615, 'dur': 75},
        'J': {'loc': 'Haight-Ashbury', 'avail_start': 210, 'avail_end': 645, 'dur': 90},
        'N': {'loc': 'Marina District', 'avail_start': 120, 'avail_end': 675, 'dur': 105},
        'K': {'loc': 'Nob Hill', 'avail_start': 735, 'avail_end': 765, 'dur': 30}
    }
    
    # Map friend symbols to their details
    loc_map = {f: friends[f]['loc'] for f in friends}
    dur_map = {f: friends[f]['dur'] for f in friends}
    avail_start_map = {f: friends[f]['avail_start'] for f in friends}
    avail_end_map = {f: friends[f]['avail_end'] for f in friends}
    start_map = {
        'S': start_S,
        'J': start_J,
        'N': start_N,
        'K': start_K
    }
    meet_map = {
        'S': meet_S,
        'J': meet_J,
        'N': meet_N,
        'K': meet_K
    }
    
    # Constraints for each friend if met
    for f in ['S', 'J', 'N', 'K']:
        loc = loc_map[f]
        # Start time must be at least travel time from Union Square
        s.add(Implies(meet_map[f], start_map[f] >= travel_from_U[loc]))
        # Start time must be within availability window
        s.add(Implies(meet_map[f], start_map[f] >= avail_start_map[f]))
        # Meeting must end before availability window closes
        s.add(Implies(meet_map[f], start_map[f] + dur_map[f] <= avail_end_map[f]))
    
    # Karen must start exactly at 735 minutes if met
    s.add(Implies(meet_K, start_K == 735))
    
    # Pairwise constraints for every pair of distinct friends
    friend_list = ['S', 'J', 'N', 'K']
    for i in range(len(friend_list)):
        for j in range(i + 1, len(friend_list)):
            f1 = friend_list[i]
            f2 = friend_list[j]
            loc1 = loc_map[f1]
            loc2 = loc_map[f2]
            # Travel times between the two locations
            t12 = travel_times[loc1][loc2]
            t21 = travel_times[loc2][loc1]
            # If both friends are met, add disjunctive constraint
            both_met = And(meet_map[f1], meet_map[f2])
            # Option 1: f1 before f2
            option1 = (start_map[f1] + dur_map[f1] + t12 <= start_map[f2])
            # Option 2: f2 before f1
            option2 = (start_map[f2] + dur_map[f2] + t21 <= start_map[f1])
            s.add(Implies(both_met, Or(option1, option2)))
    
    # Maximize the number of friends met
    num_met = meet_S + meet_J + meet_N + meet_K
    s.maximize(num_met)
    
    # Check satisfiability and retrieve the model
    if s.check() == sat:
        m = s.model()
        # Extract the meeting status and start times
        result = {}
        for f in friend_list:
            met = is_true(m[meet_map[f]])
            start_val = m[start_map[f]]
            if isinstance(start_val, ArithRef):
                start_val = start_val.as_fraction().numerator / start_val.as_fraction().denominator
            else:
                start_val = float(start_val.numerator_as_long()) / float(start_val.denominator_as_long())
            result[f] = {'met': met, 'start': start_val}
        
        # Print the schedule
        print("SOLUTION:")
        for f in friend_list:
            if result[f]['met']:
                # Convert start time from minutes to time of day
                total_minutes = int(round(result[f]['start']))
                hours = 9 + total_minutes // 60
                minutes = total_minutes % 60
                am_pm = "AM" if hours < 12 else "PM"
                if hours > 12:
                    hours -= 12
                print(f"Meet {'Sandra' if f=='S' else 'Joseph' if f=='J' else 'Nancy' if f=='N' else 'Karen'} at {int(hours)}:{minutes:02d} {am_pm} for {dur_map[f]} minutes.")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()