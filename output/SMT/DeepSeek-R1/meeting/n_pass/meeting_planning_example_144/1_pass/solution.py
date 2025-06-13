from z3 import *

def min_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    am_pm = "AM"
    if h >= 12:
        am_pm = "PM"
        if h > 12:
            h -= 12
    if h == 0:
        h = 12
    return f"{h}:{m:02d} {am_pm}"

def main():
    s = Solver()
    
    order = Int('order')
    s.add(Or(order == 0, order == 1))
    
    T1_arrive = If(order == 0, 540 + 7, 540 + 20)
    
    first_start = Int('first_start')
    first_end = Int('first_end')
    
    s.add(If(order == 0,
             And(first_start >= T1_arrive, first_start >= 735, 
                 first_end == first_start + 75, first_end <= 1185),
             And(first_start >= T1_arrive, first_start >= 750,
                 first_end == first_start + 30, first_end <= 885)
          ))
    
    T2_arrive = first_end + 17
    
    second_start = Int('second_start')
    second_end = Int('second_end')
    
    s.add(If(order == 0,
             And(second_start >= T2_arrive, second_start >= 750,
                 second_end == second_start + 30, second_end <= 885),
             And(second_start >= T2_arrive, second_start >= 735,
                 second_end == second_start + 75, second_end <= 1185)
          ))
    
    if s.check() == sat:
        m = s.model()
        ord_val = m[order].as_long()
        first_start_val = m[first_start].as_long()
        first_end_val = m[first_end].as_long()
        second_start_val = m[second_start].as_long()
        second_end_val = m[second_end].as_long()
        
        print("SOLUTION:")
        print("Start at The Castro at 9:00 AM.")
        if ord_val == 0:
            print(f"Travel to Mission District (7 minutes). Arrive at {min_to_time(540+7)}.")
            print(f"Meet Laura from {min_to_time(first_start_val)} to {min_to_time(first_end_val)} at Mission District.")
            print(f"Travel to Financial District (17 minutes). Arrive at {min_to_time(first_end_val+17)}.")
            print(f"Meet Anthony from {min_to_time(second_start_val)} to {min_to_time(second_end_val)} at Financial District.")
        else:
            print(f"Travel to Financial District (20 minutes). Arrive at {min_to_time(540+20)}.")
            print(f"Meet Anthony from {min_to_time(first_start_val)} to {min_to_time(first_end_val)} at Financial District.")
            print(f"Travel to Mission District (17 minutes). Arrive at {min_to_time(first_end_val+17)}.")
            print(f"Meet Laura from {min_to_time(second_start_val)} to {min_to_time(second_end_val)} at Mission District.")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()