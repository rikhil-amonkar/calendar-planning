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

    # Precompute travel times from start (Union Square) to each friend
    start_to_f = {}
    for f in range(len(friends_info)):
        loc_idx = friends_info[f][2]
        start_to_f[f] = travel[0][loc_idx]

    # Precompute travel times between every pair of friends
    travel_between = [[0] * len(friends_info) for _ in range(len(friends_info))]
    for i in range(len(friends_info)):
        loc_i = friends_info[i][2]
        for j in range(len(friends_info)):
            loc_j = friends_info[j][2]
            travel_between[i][j] = travel[loc_i][loc_j]

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
    T_res = None
    chosen_subset = None

    for subset in all_subsets:
        k = len(subset)
        s = Solver()
        
        # Order variables: o0, o1, ... o_{k-1}
        o = [Int(f'o_{i}') for i in range(k)]
        # Start times for each meeting in the sequence
        T = IntVector(f'T', k)
        
        # Constraints: each o[i] is in the subset and all distinct
        for i in range(k):
            s.add(Or([o[i] == f for f in subset]))
        s.add(Distinct(o))
        
        # First meeting: must be after traveling from start
        first_constraints = []
        for f in subset:
            first_constraints.append(And(o[0] == f, T[0] >= start_to_f[f]))
        s.add(Or(first_constraints))
        
        # Subsequent meetings: must account for travel time and previous meeting duration
        for j in range(1, k):
            consec_constraints = []
            for f_prev in subset:
                for f_curr in subset:
                    if f_prev == f_curr:
                        continue
                    # Travel time from f_prev to f_curr and duration of meeting with f_prev
                    travel_time = travel_between[f_prev][f_curr]
                    dur_prev = friends_info[f_prev][5]
                    consec_constraints.append(And(
                        o[j-1] == f_prev,
                        o[j] == f_curr,
                        T[j] >= T[j-1] + dur_prev + travel_time
                    ))
            s.add(Or(consec_constraints))
        
        # Time window constraints for each meeting
        for j in range(k):
            for f in subset:
                window_low = friends_info[f][3]
                window_high = friends_info[f][4]
                min_dur = friends_info[f][5]
                s.add(Implies(o[j] == f, T[j] >= window_low))
                s.add(Implies(o[j] == f, T[j] + min_dur <= window_high))
        
        # Check satisfiability
        if s.check() == sat:
            model = s.model()
            found = True
            model_res = model
            order_res = o
            T_res = T
            chosen_subset = subset
            break
    
    # Output results
    if not found:
        print("No valid schedule found to meet any friends.")
    else:
        k = len(chosen_subset)
        print(f"We can meet {k} friends: {', '.join(friends_info[f][1] for f in chosen_subset)}")
        print("Schedule:")
        # Extract the order and start times
        order_vals = [model_res.evaluate(o_i).as_long() for o_i in order_res]
        T_vals = [model_res.evaluate(T[j]).as_long() for j in range(k)]
        
        for idx in range(k):
            friend_idx = order_vals[idx]
            start_min = T_vals[idx]
            duration = friends_info[friend_idx][5]
            end_min = start_min + duration
            start_str = min_to_time(start_min)
            end_str = min_to_time(end_min)
            friend_name = friends_info[friend_idx][1]
            location = [name for name, idx_val in loc_index_map.items() if idx_val == friends_info[friend_idx][2]][0]
            print(f"  {idx+1}: Meet {friend_name} at {location} from {start_str} to {end_str}")

if __name__ == '__main__':
    main()