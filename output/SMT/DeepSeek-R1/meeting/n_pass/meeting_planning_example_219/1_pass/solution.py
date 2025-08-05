from z3 import *

def main():
    # Initialize the solver and optimizer
    opt = Optimize()
    
    # Active flags for each friend
    active0 = Bool('active0')  # Emily
    active1 = Bool('active1')  # Barbara
    active2 = Bool('active2')  # William
    
    # Start times in minutes from 9:00 AM
    s0 = Real('s0')  # Emily
    s1 = Real('s1')  # Barbara
    s2 = Real('s2')  # William
    
    # Travel times dictionary
    travel_dict = {
        ('C', 'A'): 8,
        ('C', 'U'): 19,
        ('C', 'T'): 20,
        ('A', 'U'): 14,
        ('A', 'T'): 16,
        ('U', 'A'): 15,
        ('U', 'T'): 7,
        ('T', 'A'): 17,
        ('T', 'U'): 7
    }
    
    def get_travel_time(from_loc, to_loc):
        if from_loc == to_loc:
            return 0
        return travel_dict.get((from_loc, to_loc), 10000)
    
    # Constraints for Emily (0)
    opt.add(Implies(active0, And(s0 >= 165, s0 <= 270, s0 >= get_travel_time('C', 'A'))))
    
    # Constraints for Barbara (1)
    opt.add(Implies(active1, And(s1 >= 465, s1 <= 495, s1 >= get_travel_time('C', 'U'))))
    
    # Constraints for William (2)
    opt.add(Implies(active2, And(s2 == 495, s2 >= get_travel_time('C', 'T'))))
    
    # Pairwise constraints
    # Emily (A) and Barbara (U)
    opt.add(Implies(And(active0, active1),
                  s0 + 105 + get_travel_time('A', 'U') <= s1
    ))
    
    # Emily (A) and William (T)
    opt.add(Implies(And(active0, active2),
                  s0 + 105 + get_travel_time('A', 'T') <= s2
    ))
    
    # Barbara (U) and William (T)
    opt.add(Implies(And(active1, active2),
                  Or(
                      s1 + 60 + get_travel_time('U', 'T') <= s2,
                      s2 + 105 + get_travel_time('T', 'U') <= s1
                  )))
    
    # Maximize the number of active meetings
    num_meetings = If(active0, 1, 0) + If(active1, 1, 0) + If(active2, 1, 0)
    opt.maximize(num_meetings)
    
    # Check for a solution
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        
        # Process Emily
        if is_true(m[active0]):
            start_minutes = m.eval(s0)
            if is_int_value(start_minutes):
                start_val = start_minutes.as_long()
            else:
                start_val = int(str(start_minutes))
            end_val = start_val + 105
            total_minutes_start = 540 + start_val
            hours_start = total_minutes_start // 60
            minutes_start = total_minutes_start % 60
            total_minutes_end = 540 + end_val
            hours_end = total_minutes_end // 60
            minutes_end = total_minutes_end % 60
            start_str = f"{hours_start:02d}:{minutes_start:02d}"
            end_str = f"{hours_end:02d}:{minutes_end:02d}"
            itinerary.append({"action": "meet", "person": "Emily", "start_time": start_str, "end_time": end_str})
        
        # Process Barbara
        if is_true(m[active1]):
            start_minutes = m.eval(s1)
            if is_int_value(start_minutes):
                start_val = start_minutes.as_long()
            else:
                start_val = int(str(start_minutes))
            end_val = start_val + 60
            total_minutes_start = 540 + start_val
            hours_start = total_minutes_start // 60
            minutes_start = total_minutes_start % 60
            total_minutes_end = 540 + end_val
            hours_end = total_minutes_end // 60
            minutes_end = total_minutes_end % 60
            start_str = f"{hours_start:02d}:{minutes_start:02d}"
            end_str = f"{hours_end:02d}:{minutes_end:02d}"
            itinerary.append({"action": "meet", "person": "Barbara", "start_time": start_str, "end_time": end_str})
        
        # Process William
        if is_true(m[active2]):
            itinerary.append({"action": "meet", "person": "William", "start_time": "17:15", "end_time": "19:00"})
        
        # Sort itinerary by start time
        itinerary_sorted = sorted(itinerary, key=lambda x: x['start_time'])
        result = {'itinerary': itinerary_sorted}
        print(result)
    else:
        print("No solution found")

def is_int_value(v):
    return isinstance(v, IntNumRef)

if __name__ == '__main__':
    main()