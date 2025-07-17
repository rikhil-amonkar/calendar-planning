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
    s.add(start0 == travel0)
    
    dur0 = Int('dur0')
    s.add(dur0 == If(first == 0, 15, If(first == 1, 75, 90)))
    
    travel1 = Int('travel1')
    s.add(travel1 == 
          If(first == 0, 
             If(second == 1, 12, 22),
             If(first == 1,
                If(second == 0, 13, 15),
                If(second == 0, 22, 16)
             )
          )
    
    start1 = Int('start1')
    s.add(start1 == start0 + dur0 + travel1)
    
    dur1 = Int('dur1')
    s.add(dur1 == If(second == 0, 15, If(second == 1, 75, 90)))
    
    travel2 = Int('travel2')
    s.add(travel2 == 
          If(second == 0,
             If(third == 1, 12, 22),
             If(second == 1,
                If(third == 0, 13, 15),
                If(third == 0, 22, 16)
             )
          )
    
    start2 = Int('start2')
    s.add(start2 == start1 + dur1 + travel2)
    
    dur2 = Int('dur2')
    s.add(dur2 == If(third == 0, 15, If(third == 1, 75, 90)))
    
    T_d = If(first == 0, start0, If(second == 0, start1, start2))
    T_t = If(first == 1, start0, If(second == 1, start1, start2))
    T_r = If(first == 2, start0, If(second == 2, start1, start2))
    
    s.add(T_d >= 105, T_d <= 360)
    s.add(T_t >= 0, T_t <= 240)
    s.add(T_r >= 195, T_r <= 465)
    
    if s.check() == sat:
        model = s.model()
        first_val = model.eval(first).as_long()
        second_val = model.eval(second).as_long()
        third_val = model.eval(third).as_long()
        loc_names = {0: "Fisherman's Wharf", 1: "Pacific Heights", 2: "Mission District"}
        friend_names = {0: "David", 1: "Timothy", 2: "Robert"}
        
        T_d_val = model.eval(T_d).as_long()
        T_t_val = model.eval(T_t).as_long()
        T_r_val = model.eval(T_r).as_long()
        
        print("SOLUTION:")
        print(f"Order: 1. {loc_names[first_val]} ({friend_names[first_val]}), 2. {loc_names[second_val]} ({friend_names[second_val]}), 3. {loc_names[third_val]} ({friend_names[third_val]})")
        print(f"Meet David at {minutes_to_time(T_d_val)}")
        print(f"Meet Timothy at {minutes_to_time(T_t_val)}")
        print(f"Meet Robert at {minutes_to_time(T_r_val)}")
    else:
        print("SOLUTION: No feasible schedule found to meet all three friends.")

if __name__ == "__main__":
    main()