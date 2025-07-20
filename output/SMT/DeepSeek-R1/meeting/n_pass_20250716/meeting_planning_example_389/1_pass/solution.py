from itertools import combinations
from z3 import *

def main():
    # Data
    friends = [0, 1, 2, 3]  # 0: Sarah, 1: Mary, 2: Helen, 3: Thomas
    names = {
        0: "Sarah",
        1: "Mary",
        2: "Helen",
        3: "Thomas"
    }
    locations = {
        0: "Fisherman's Wharf",
        1: "Richmond District",
        2: "Mission District",
        3: "Bayview"
    }
    min_durations = [105, 75, 30, 120]  # in minutes for friends 0,1,2,3
    window_low = [345, 240, 765, 375]   # start of availability window in minutes since 9:00 AM
    window_high = [510, 615, 810, 585]  # end of availability window in minutes since 9:00 AM

    # Travel matrix: 5x5, indices: 0: Fisherman's Wharf, 1: Richmond, 2: Mission, 3: Bayview, 4: Haight-Ashbury (start)
    travel_matrix = [
        [0, 18, 22, 26, 22],
        [18, 0, 20, 26, 10],
        [22, 20, 0, 15, 12],
        [25, 25, 13, 0, 19],
        [23, 10, 11, 18, 0]
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

    # Function to get travel time between two locations (Z3 integers)
    def get_travel_z3(i, j):
        cases = []
        for a in range(5):
            for b in range(5):
                cond = And(i == a, j == b)
                cases.append((cond, travel_matrix[a][b]))
        expr = cases[-1][1]
        for idx in range(len(cases)-2, -1, -1):
            expr = If(cases[idx][0], cases[idx][1], expr)
        return expr

    # Generate subsets in decreasing order of size
    all_subsets = []
    for r in range(4, 0, -1):
        for comb in combinations(friends, r):
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
        # Start times for each friend (even if not in subset, but we'll constrain only those in subset)
        S = RealVector('S', 4)  # S0 for Sarah, S1 for Mary, S2 for Helen, S3 for Thomas
        
        # Helper functions for S_var and min_dur_var (using Z3 expressions)
        def S_var(i):
            return If(i == 0, S[0],
                   If(i == 1, S[1],
                   If(i == 2, S[2],
                   S[3])))
        
        def min_dur_var(i):
            return If(i == 0, min_durations[0],
                   If(i == 1, min_durations[1],
                   If(i == 2, min_durations[2],
                   min_durations[3])))
        
        # Constraints for order: distinct and each in the subset
        s.add(Distinct(o))
        for j in range(k):
            s.add(Or([o[j] == f for f in subset]))
        
        # Chain constraints for travel and meeting durations
        # First meeting: must be after traveling from start (index4) to the first location
        s.add(S_var(o[0]) >= get_travel_z3(4, o[0]))
        for j in range(1, k):
            s.add(S_var(o[j]) >= S_var(o[j-1]) + min_dur_var(o[j-1]) + get_travel_z3(o[j-1], o[j]))
        
        # Window constraints for each friend in the subset
        for f in subset:
            s.add(S[f] >= window_low[f])
            s.add(S[f] + min_dur_var(f) <= window_high[f])
        
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
        print(f"We can meet {len(chosen_subset)} friends: {', '.join(names[f] for f in chosen_subset)}")
        print("Schedule:")
        # Evaluate the order
        order_eval = [model_res.evaluate(order_res[j]).as_long() for j in range(k_res)]
        # For each meeting in the order
        for idx, friend_idx in enumerate(order_eval):
            start_val = model_res.evaluate(S_res[friend_idx])
            # Convert start_val to integer minutes
            if is_rational_value(start_val):
                num = start_val.numerator_as_long()
                den = start_val.denominator_as_long()
                start_min = num // den
            elif is_int_value(start_val):
                start_min = start_val.as_long()
            else:
                start_min = int(float(str(start_val)))
            duration = min_durations[friend_idx]
            end_min = start_min + duration
            start_str = min_to_time(start_min)
            end_str = min_to_time(end_min)
            print(f"  {idx+1}: Meet {names[friend_idx]} at {locations[friend_idx]} from {start_str} to {end_str}")

if __name__ == '__main__':
    main()