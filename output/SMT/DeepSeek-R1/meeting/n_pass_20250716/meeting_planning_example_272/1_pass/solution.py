from z3 import *

def min_to_time(total_mins):
    total_minutes_from_9am = total_mins
    total_minutes_from_midnight = 9 * 60 + total_minutes_from_9am
    hours = total_minutes_from_midnight // 60
    minutes = total_minutes_from_midnight % 60
    hours_mod = hours % 24
    period = "AM" if hours_mod < 12 else "PM"
    hours12 = hours_mod % 12
    if hours12 == 0:
        hours12 = 12
    return f"{hours12}:{minutes:02d} {period}"

def main():
    travel = {
        ('RH', 'NH'): 5,
        ('RH', 'MD'): 16,
        ('RH', 'EM'): 8,
        ('NH', 'RH'): 5,
        ('NH', 'MD'): 13,
        ('NH', 'EM'): 9,
        ('MD', 'RH'): 15,
        ('MD', 'NH'): 12,
        ('MD', 'EM'): 19,
        ('EM', 'RH'): 8,
        ('EM', 'NH'): 10,
        ('EM', 'MD'): 20
    }
    
    meet_p, meet_a, meet_t = Bools('meet_p meet_a meet_t')
    start_p, start_a, start_t = Ints('start_p start_a start_t')
    dur_p, dur_a, dur_t = Ints('dur_p dur_a dur_t')
    before_p_a, before_p_t, before_a_t = Bools('before_p_a before_p_t before_a_t')
    
    s = Optimize()
    
    constraints = []
    
    # Duration and meeting time constraints
    constraints.append(If(meet_p, And(dur_p >= 90, start_p >= 570, start_p + dur_p <= 765), True))
    constraints.append(If(meet_a, And(dur_a >= 45, start_a >= 690, start_a + dur_a <= 735), True))
    constraints.append(If(meet_t, And(dur_t >= 120, start_t >= 45, start_t + dur_t <= 525), True))
    
    # Non-negative durations
    constraints.append(If(meet_p, dur_p >= 0, True))
    constraints.append(If(meet_a, dur_a >= 0, True))
    constraints.append(If(meet_t, dur_t >= 0, True))
    
    # Pairwise constraints for travel times
    constraints.append(If(And(meet_p, meet_a),
                         If(before_p_a, 
                            start_p + dur_p + travel[('NH', 'MD')] <= start_a,
                            start_a + dur_a + travel[('MD', 'NH')] <= start_p),
                         True))
    
    constraints.append(If(And(meet_p, meet_t),
                         If(before_p_t,
                            start_p + dur_p + travel[('NH', 'EM')] <= start_t,
                            start_t + dur_t + travel[('EM', 'NH')] <= start_p),
                         True))
    
    constraints.append(If(And(meet_a, meet_t),
                         If(before_a_t,
                            start_a + dur_a + travel[('MD', 'EM')] <= start_t,
                            start_t + dur_t + travel[('EM', 'MD')] <= start_a),
                         True))
    
    # First meeting constraints
    cond_p = And(If(meet_a, before_p_a, True), If(meet_t, before_p_t, True))
    constraints.append(If(meet_p, Implies(cond_p, start_p >= travel[('RH', 'NH')]), True))
    
    cond_a = And(If(meet_p, Not(before_p_a), True), If(meet_t, before_a_t, True))
    constraints.append(If(meet_a, Implies(cond_a, start_a >= travel[('RH', 'MD')]), True))
    
    cond_t = And(If(meet_p, Not(before_p_t), True), If(meet_a, Not(before_a_t), True))
    constraints.append(If(meet_t, Implies(cond_t, start_t >= travel[('RH', 'EM')]), True))
    
    s.add(constraints)
    
    count = If(meet_p, 1, 0) + If(meet_a, 1, 0) + If(meet_t, 1, 0)
    s.maximize(count)
    
    if s.check() == sat:
        m = s.model()
        num_meetings = m.eval(count).as_long()
        print(f"Maximum number of meetings: {num_meetings}")
        
        if is_true(m[meet_p]):
            start_val = m[start_p].as_long()
            dur_val = m[dur_p].as_long()
            print(f"Meet Patricia at Nob Hill from {min_to_time(start_val)} to {min_to_time(start_val + dur_val)} for {dur_val} minutes.")
        
        if is_true(m[meet_a]):
            start_val = m[start_a].as_long()
            dur_val = m[dur_a].as_long()
            print(f"Meet Ashley at Mission District from {min_to_time(start_val)} to {min_to_time(start_val + dur_val)} for {dur_val} minutes.")
        
        if is_true(m[meet_t]):
            start_val = m[start_t].as_long()
            dur_val = m[dur_t].as_long()
            print(f"Meet Timothy at Embarcadero from {min_to_time(start_val)} to {min_to_time(start_val + dur_val)} for {dur_val} minutes.")
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()