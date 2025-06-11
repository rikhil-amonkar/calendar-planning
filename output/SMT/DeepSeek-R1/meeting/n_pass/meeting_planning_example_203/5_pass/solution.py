from z3 import Solver, Int, Distinct, If, Or, And, sat

def minutes_to_time(minutes):
    total_minutes = minutes
    hours = total_minutes // 60
    mins = total_minutes % 60
    total_hours = 9 + hours
    if total_hours < 12:
        am_pm = "AM"
        hour_str = total_hours
    elif total_hours == 12:
        am_pm = "PM"
        hour_str = 12
    elif total_hours == 24:
        am_pm = "AM"
        hour_str = 12
    else:
        am_pm = "PM"
        hour_str = total_hours - 12
    return f"{hour_str}:{mins:02d}{am_pm}"

def main():
    s = Solver()
    
    first = Int('first')
    second = Int('second')
    third = Int('third')
    
    s.add(Distinct(first, second, third))
    s.add(Or(first == 0, first == 1, first == 2))
    s.add(Or(second == 0, second == 1, second == 2))
    s.add(Or(third == 0, third == 1, third == 2))
    
    travel0 = Int('travel0')
    s.add(travel0 == If(first == 0, 10, If(first == 1, 13, 17)))
    
    start0 = Int('start0')
    dur0 = If(first == 0, 15, If(first == 1, 75, 90))
    s.add(start0 >= travel0)
    s.add(start0 >= If(first == 0, 105, If(first == 1, 0, 195)))
    s.add(start0 + dur0 <= If(first == 0, 375, If(first == 1, 315, 555)))
    
    travel1 = Int('travel1')
    travel1_expr = If(first == 0, 
                     If(second == 1, 12, 22),
                     If(first == 1,
                        If(second == 0, 13, 15),
                        If(second == 0, 22, 16)
                     )
                  )
    s.add(travel1 == travel1_expr)
    
    start1 = Int('start1')
    dur1 = If(second == 0, 15, If(second == 1, 75, 90))
    s.add(start1 >= start0 + dur0 + travel1)
    s.add(start1 >= If(second == 0, 105, If(second == 1, 0, 195)))
    s.add(start1 + dur1 <= If(second == 0, 375, If(second == 1, 315, 555)))
    
    travel2 = Int('travel2')
    travel2_expr = If(second == 0,
                     If(third == 1, 12, 22),
                     If(second == 1,
                        If(third == 0, 13, 15),
                        If(third == 0, 22, 16)
                     )
                  )
    s.add(travel2 == travel2_expr)
    
    start2 = Int('start2')
    dur2 = If(third == 0, 15, If(third == 1, 75, 90))
    s.add(start2 >= start1 + dur1 + travel2)
    s.add(start2 >= If(third == 0, 105, If(third == 1, 0, 195)))
    s.add(start2 + dur2 <= If(third == 0, 375, If(third == 1, 315, 555)))
    
    if s.check() == sat:
        model = s.model()
        first_val = model.eval(first).as_long()
        second_val = model.eval(second).as_long()
        third_val = model.eval(third).as_long()
        loc_names = {0: "Fisherman's Wharf", 1: "Pacific Heights", 2: "Mission District"}
        friend_names = {0: "David", 1: "Timothy", 2: "Robert"}
        
        start0_val = model.eval(start0).as_long()
        start1_val = model.eval(start1).as_long()
        start2_val = model.eval(start2).as_long()
        
        print("SOLUTION:")
        print(f"Order: 1. {loc_names[first_val]} ({friend_names[first_val]}), 2. {loc_names[second_val]} ({friend_names[second_val]}), 3. {loc_names[third_val]} ({friend_names[third_val]})")
        print(f"Meet {friend_names[first_val]} at {minutes_to_time(start0_val)}")
        print(f"Meet {friend_names[second_val]} at {minutes_to_time(start1_val)}")
        print(f"Meet {friend_names[third_val]} at {minutes_to_time(start2_val)}")
    else:
        print("SOLUTION: No feasible schedule found to meet all three friends.")

if __name__ == "__main__":
    main()