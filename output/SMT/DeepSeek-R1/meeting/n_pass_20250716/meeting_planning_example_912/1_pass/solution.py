from itertools import combinations
from z3 import *

def main():
    # Map location names to indices
    loc_index_map = {
        "Union Square": 0,
        "Presidio": 1,
        "Alamo Square": 2,
        "Marina District": 3,
        "Financial District": 4,
        "Nob Hill": 5,
        "Sunset District": 6,
        "Chinatown": 7,
        "Russian Hill": 8,
        "North Beach": 9,
        "Haight-Ashbury": 10
    }

    # Build travel time matrix (11x11)
    travel = [
        [0, 24, 15, 18, 9, 9, 27, 7, 13, 10, 18],
        [22, 0, 19, 11, 23, 18, 15, 21, 14, 18, 15],
        [14, 17, 0, 15, 17, 11, 16, 15, 13, 15, 5],
        [16, 10, 15, 0, 17, 12, 19, 15, 8, 11, 16],
        [9, 22, 17, 15, 0, 8, 30, 5, 11, 7, 19],
        [7, 17, 11, 11, 9, 0, 24, 6, 5, 8, 13],
        [30, 16, 17, 21, 30, 27, 0, 30, 24, 28, 15],
        [7, 19, 17, 12, 5, 9, 29, 0, 7, 3, 19],
        [10, 14, 15, 7, 11, 5, 23, 9, 0, 5, 17],
        [7, 17, 16, 9, 8, 7, 27, 6, 4, 0, 18],
        [19, 15, 5, 17, 21, 15, 15, 19, 17, 19, 0]
    ]

    # Friends data: (friend_index, name, location_index, window_low, window_high, min_duration)
    friends_info = [
        (0, "Kimberly", loc_index_map["Presidio"], 390, 420, 15),
        (1, "Elizabeth", loc_index_map["Alamo Square"], 615, 675, 15),
        (2, "Joshua", loc_index_map["Marina District"], 90, 315, 45),
        (3, "Sandra", loc_index_map["Financial District"], 630, 675, 45),
        (4, "Kenneth", loc_index_map["Nob Hill"], 225, 765, 30),
        (5, "Betty", loc_index_map["Sunset District"], 300, 600, 60),
        (6, "Deborah", loc_index_map["Chinatown"], 495, 690, 15),
        (7, "Barbara", loc_index_map["Russian Hill"], 510, 735, 120),
        (8, "Steven", loc_index_map["North Beach"], 525, 705, 90),
        (9, "Daniel", loc_index_map["Haight-Ashbury"], 570, 585, 15)
    ]

    # Helper function to convert minutes since 9:00 AM to time string
    def min_to_time(mins):
        total_minutes = 9 * 60 + mins
        hours = total_minutes // 60
        mins_part = total_minutes % 60
        if hours >= 13:
            suffix = "PM"
            hours12 = hours - 12
        elif hours == 12:
            suffix = "PM"
            hours12 = 12
        else:
            suffix = "AM"
            hours12 = hours
        return f"{hours12}:{mins_part:02d} {suffix}"

    # Function to get travel time between two friend indices
    def get_travel_time(friend_i, friend_j):
        loc_i = friends_info[friend_i][2]
        loc_j = friends_info[friend_j][2]
        return travel[loc_i][loc_j]

    # Generate subsets in decreasing order of size
    all_friend_indices = list(range(len(friends_info)))
    all_subsets = []
    for r in range(len(all_friend_indices), 0, -1):
        for comb in combinations(all_friend_indices, r):
            all_subsets.append(comb)

    # Try each subset
    found = False
    model_res = None
    order_res = None
    S_res = None
    chosen_subset = None
    k_res = 0

    for subset in all_subsets:
        k = len(subset)
        s = Solver()
        
        # Order variables: o0, o1, ... o_{k-1}
        o = [Int(f'o_{i}') for i in range(k)]
        # Start times for each friend (for all 10 friends, but we only constrain those in the subset)
        S = RealVector('S', len(friends_info))  # S0, S1, ... S9
        
        # Constraints for order: distinct and each in the subset
        s.add(Distinct(o))
        for j in range(k):
            s.add(Or([o[j] == f for f in subset]))
        
        # Helper function to get location index of a friend index
        def get_loc_idx(friend_idx):
            return friends_info[friend_idx][2]
        
        # Chain constraints for travel and meeting durations
        # First meeting: must be after traveling from start (Union Square, index0) to the first friend's location
        first_friend = o[0]
        loc_first = get_loc_idx(first_friend)
        travel_time_first = travel[0][loc_first]  # from Union Square (0) to the first friend's location
        s.add(S[first_friend] >= travel_time_first)
        
        for j in range(1, k):
            prev_friend = o[j-1]
            curr_friend = o[j]
            # Travel time from previous friend's location to current friend's location
            travel_time = get_travel_time(prev_friend, curr_friend)
            # The current meeting must start after the previous meeting ends plus travel time
            s.add(S[curr_friend] >= S[prev_friend] + friends_info[prev_friend][5] + travel_time)
        
        # Window constraints for each friend in the subset
        for f in subset:
            s.add(S[f] >= friends_info[f][3])
            s.add(S[f] + friends_info[f][5] <= friends_info[f][4])
        
        # Check satisfiability
        if s.check() == sat:
            model = s.model()
            found = True
            model_res = model
            order_res = o
            S_res = S
            chosen_subset = subset
            k_res = k
            break
    
    # Output results
    if not found:
        print("No valid schedule found to meet any friends.")
    else:
        print(f"We can meet {len(chosen_subset)} friends: {', '.join(friends_info[f][1] for f in chosen_subset)}")
        print("Schedule:")
        # Evaluate the order
        order_eval = []
        for j in range(k_res):
            o_val = model_res.evaluate(order_res[j])
            if is_int_value(o_val):
                order_eval.append(o_val.as_long())
            else:
                # If Z3 returns a constant expression
                order_eval.append(int(str(o_val)))
        # For each meeting in the order
        for idx, friend_idx in enumerate(order_eval):
            s_val = model_res.evaluate(S_res[friend_idx])
            # Convert s_val to integer minutes
            if is_rational_value(s_val):
                num = s_val.numerator_as_long()
                den = s_val.denominator_as_long()
                start_min = num // den
            elif is_int_value(s_val):
                start_min = s_val.as_long()
            else:
                # Fallback: try converting the string representation to float then int
                start_min = int(float(str(s_val)))
            duration = friends_info[friend_idx][5]
            end_min = start_min + duration
            start_str = min_to_time(start_min)
            end_str = min_to_time(end_min)
            friend_name = friends_info[friend_idx][1]
            location = [name for name, idx_val in loc_index_map.items() if idx_val == friends_info[friend_idx][2]][0]
            print(f"  {idx+1}: Meet {friend_name} at {location} from {start_str} to {end_str}")

if __name__ == '__main__':
    main()