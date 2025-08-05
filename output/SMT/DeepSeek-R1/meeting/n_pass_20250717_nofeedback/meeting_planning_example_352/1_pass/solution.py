from z3 import *

def main():
    # Define travel times
    travel_U = {'C': 7, 'H': 18, 'M': 18}
    travel_between = {
        ('C', 'H'): 19, ('C', 'M'): 12,
        ('H', 'C'): 19, ('H', 'M'): 17,
        ('M', 'C'): 16, ('M', 'H'): 16
    }
    travel_to_N = {'C': 8, 'H': 15, 'M': 12}
    
    # Z3 variables for the order of meetings (0: Sandra, 1: Joseph, 2: Nancy)
    p0, p1, p2 = Ints('p0 p1 p2')
    S0, S1, S2 = Ints('S0 S1 S2')  # Start times in minutes after 9:00 AM
    
    # Permutation constraints: p0, p1, p2 must be a permutation of 0,1,2
    perm = And(p0 >= 0, p0 <= 2, p1 >= 0, p1 <= 2, p2 >= 0, p2 <= 2,
               p0 != p1, p0 != p2, p1 != p2)
    
    # Time window constraints for each friend
    # Sandra: max_start = 540 (because 540+75=615, which is 7:15 PM)
    # Joseph: min_start=210 (12:30 PM), max_start=555 (555+90=645 -> 7:45 PM)
    # Nancy: min_start=120 (11:00 AM), max_start=570 (570+105=675 -> 8:15 PM)
    min0 = If(p0 == 1, 210, If(p0 == 2, 120, 0))
    max0 = If(p0 == 0, 540, If(p0 == 1, 555, 570))
    min1 = If(p1 == 1, 210, If(p1 == 2, 120, 0))
    max1 = If(p1 == 0, 540, If(p1 == 1, 555, 570))
    min2 = If(p2 == 1, 210, If(p2 == 2, 120, 0))
    max2 = If(p2 == 0, 540, If(p2 == 1, 555, 570))
    
    # Durations for each friend
    dur0 = If(p0 == 0, 75, If(p0 == 1, 90, 105))
    dur1 = If(p1 == 0, 75, If(p1 == 1, 90, 105))
    dur2 = If(p2 == 0, 75, If(p2 == 1, 90, 105))
    
    # Travel time for the first meeting (from Union Square to the first location)
    travel0 = If(p0 == 0, travel_U['C'], If(p0 == 1, travel_U['H'], travel_U['M']))
    
    # Travel time between first and second meeting
    travel1 = If(And(p0 == 0, p1 == 1), 19,
                If(And(p0 == 0, p1 == 2), 12,
                If(And(p0 == 1, p1 == 0), 19,
                If(And(p0 == 1, p1 == 2), 17,
                If(And(p0 == 2, p1 == 0), 16,
                If(And(p0 == 2, p1 == 1), 16, 0))))))
    
    # Travel time between second and third meeting
    travel2 = If(And(p1 == 0, p2 == 1), 19,
                If(And(p1 == 0, p2 == 2), 12,
                If(And(p1 == 1, p2 == 0), 19,
                If(And(p1 == 1, p2 == 2), 17,
                If(And(p1 == 2, p2 == 0), 16,
                If(And(p1 == 2, p2 == 1), 16, 0))))))
    
    # Travel time from the third meeting to Nob Hill (for Karen)
    travel3 = If(p2 == 0, travel_to_N['C'], If(p2 == 1, travel_to_N['H'], travel_to_N['M']))
    
    # Constraints for start times and travel
    c0 = And(S0 >= min0, S0 <= max0, S0 >= travel0)
    c1 = And(S1 >= min1, S1 <= max1, S1 >= S0 + dur0 + travel1)
    c2 = And(S2 >= min2, S2 <= max2, S2 >= S1 + dur1 + travel2)
    c_end = S2 + dur2 + travel3 <= 735  # Must reach Nob Hill by 9:15 PM (735 minutes from 9:00 AM)
    nonneg = And(S0 >= 0, S1 >= 0, S2 >= 0)
    
    # Combine all constraints
    s = Solver()
    s.add(perm, c0, c1, c2, c_end, nonneg)
    
    if s.check() == sat:
        m = s.model()
        p0_val = m[p0].as_long()
        p1_val = m[p1].as_long()
        p2_val = m[p2].as_long()
        S0_val = m[S0].as_long()
        S1_val = m[S1].as_long()
        S2_val = m[S2].as_long()
        
        # Map meeting indices to friend names
        friends = {0: 'Sandra', 1: 'Joseph', 2: 'Nancy'}
        friend0 = friends[p0_val]
        friend1 = friends[p1_val]
        friend2 = friends[p2_val]
        
        # Durations for each meeting
        durs = {0:75, 1:90, 2:105}
        dur0_val = durs[p0_val]
        dur1_val = durs[p1_val]
        dur2_val = durs[p2_val]
        
        # Calculate end times
        end0 = S0_val + dur0_val
        end1 = S1_val + dur1_val
        end2 = S2_val + dur2_val
        
        # Convert minutes to HH:MM format (relative to 9:00 AM)
        def min_to_time(mins):
            total_mins = 540 + mins  # 9:00 AM is 540 minutes from midnight
            h = total_mins // 60
            m = total_mins % 60
            return f"{h:02d}:{m:02d}"
        
        # Karen's meeting (fixed)
        karen_start = 735
        karen_end = 765
        
        # Create itinerary in chronological order
        itinerary = [
            {"action": "meet", "person": friend0, "start_time": min_to_time(S0_val), "end_time": min_to_time(end0)},
            {"action": "meet", "person": friend1, "start_time": min_to_time(S1_val), "end_time": min_to_time(end1)},
            {"action": "meet", "person": friend2, "start_time": min_to_time(S2_val), "end_time": min_to_time(end2)},
            {"action": "meet", "person": "Karen", "start_time": min_to_time(karen_start), "end_time": min_to_time(karen_end)}
        ]
        
        # Output as JSON
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()