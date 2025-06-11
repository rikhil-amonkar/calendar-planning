from z3 import *

def main():
    # Initialize the optimizer
    opt = Optimize()
    
    # Meeting start times in minutes from 9:00 AM
    s_c, s_r, s_k = Reals('s_c s_r s_k')
    
    # Boolean variables to indicate if we meet each friend
    meet_c, meet_r, meet_k = Bools('meet_c meet_r meet_k')
    
    # Position variables for the sequence of meetings
    p_c, p_r, p_k = Ints('p_c p_r p_k')
    
    # Travel times from Union Square to each district
    travel_US_SD = 26  # Union Square to Sunset District
    travel_US_MD = 14  # Union Square to Mission District
    travel_US_BV = 15  # Union Square to Bayview
    
    # Travel times between districts
    travel_between = {
        ('c', 'r'): 24,  # Sunset District to Mission District
        ('c', 'k'): 22,  # Sunset District to Bayview
        ('r', 'c'): 24,  # Mission District to Sunset District
        ('r', 'k'): 15,  # Mission District to Bayview
        ('k', 'c'): 23,  # Bayview to Sunset District
        ('k', 'r'): 13   # Bayview to Mission District
    }
    
    # Meeting durations in minutes
    dur_c = 30
    dur_r = 120
    dur_k = 120
    
    # Time window constraints
    opt.add(Implies(meet_c, And(s_c >= 75, s_c <= 135)))      # 10:15 AM to 11:45 AM
    opt.add(Implies(meet_r, And(s_r >= 150, s_r <= 555)))     # 11:30 AM to 8:15 PM
    opt.add(Implies(meet_k, And(s_k >= 225, s_k <= 240)))     # 12:45 PM to 3:00 PM
    
    # Number of meetings
    n = If(meet_c, 1, 0) + If(meet_r, 1, 0) + If(meet_k, 1, 0)
    
    # Position constraints for meetings that occur
    opt.add(Implies(meet_c, And(p_c >= 0, p_c <= n - 1)))
    opt.add(Implies(meet_r, And(p_r >= 0, p_r <= n - 1)))
    opt.add(Implies(meet_k, And(p_k >= 0, p_k <= n - 1)))
    
    # Distinct positions for meetings that occur
    opt.add(Implies(And(meet_c, meet_r), p_c != p_r))
    opt.add(Implies(And(meet_c, meet_k), p_c != p_k))
    opt.add(Implies(And(meet_r, meet_k), p_r != p_k))
    
    # Travel constraints between consecutive meetings
    friends = [('c', meet_c, s_c, dur_c), ('r', meet_r, s_r, dur_r), ('k', meet_k, s_k, dur_k)]
    for i_idx, (i, meet_i, s_i, dur_i) in enumerate(friends):
        for j_idx, (j, meet_j, s_j, dur_j) in enumerate(friends):
            if i == j:
                continue
            travel_time = travel_between[(i, j)]
            opt.add(Implies(And(meet_i, meet_j, p_j == p_i + 1),
                             s_j >= s_i + dur_i + travel_time))
    
    # First meeting constraints (travel from Union Square)
    opt.add(Implies(meet_c, If(p_c == 0, s_c >= travel_US_SD, True)))
    opt.add(Implies(meet_r, If(p_r == 0, s_r >= travel_US_MD, True)))
    opt.add(Implies(meet_k, If(p_k == 0, s_k >= travel_US_BV, True)))
    
    # Maximize the number of meetings
    opt.maximize(n)
    
    # Check for a solution
    if opt.check() == sat:
        m = opt.model()
        # Convert minutes to time string
        def minutes_to_time(minutes):
            total_minutes = int(minutes)
            hours = total_minutes // 60
            minutes = total_minutes % 60
            time_str = f"{9 + hours}:{minutes:02d}"
            if hours >= 4:  # After 1:00 PM
                time_str += "PM"
            else:
                time_str += "AM"
            return time_str
        
        # Print results
        print("SOLUTION:")
        meet_c_val = m.eval(meet_c)
        meet_r_val = m.eval(meet_r)
        meet_k_val = m.eval(meet_k)
        
        if meet_c_val:
            s_c_val = m.eval(s_c)
            if is_algebraic_value(s_c_val):
                s_c_val = s_c_val.approx().as_long()
            else:
                s_c_val = s_c_val.as_long()
            end_c = s_c_val + dur_c
            print(f"Meet Carol at Sunset District from {minutes_to_time(s_c_val)} to {minutes_to_time(end_c)}")
        
        if meet_r_val:
            s_r_val = m.eval(s_r)
            if is_algebraic_value(s_r_val):
                s_r_val = s_r_val.approx().as_long()
            else:
                s_r_val = s_r_val.as_long()
            end_r = s_r_val + dur_r
            print(f"Meet Rebecca at Mission District from {minutes_to_time(s_r_val)} to {minutes_to_time(end_r)}")
        
        if meet_k_val:
            s_k_val = m.eval(s_k)
            if is_algebraic_value(s_k_val):
                s_k_val = s_k_val.approx().as_long()
            else:
                s_k_val = s_k_val.as_long()
            end_k = s_k_val + dur_k
            print(f"Meet Karen at Bayview from {minutes_to_time(s_k_val)} to {minutes_to_time(end_k)}")
        
        num_met = (1 if meet_c_val else 0) + (1 if meet_r_val else 0) + (1 if meet_k_val else 0)
        print(f"Total friends met: {num_met}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()