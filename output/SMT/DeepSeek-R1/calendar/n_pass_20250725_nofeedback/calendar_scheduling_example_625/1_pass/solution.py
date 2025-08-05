from z3 import *

def main():
    d = Int('d')
    start_minutes = Int('start_minutes')
    
    s = Optimize()
    
    s.add(Or(d == 0, d == 1))
    s.add(start_minutes >= 540)  # 9:00 in minutes (9*60)
    s.add(start_minutes <= 990)  # 16:30 in minutes (16*60 + 30)
    
    # Monday constraint: only free from 10:00 to 10:30 (600 to 630 minutes)
    monday_constraint = And(d == 0, start_minutes == 600)
    
    # Tuesday constraints: free slots between busy times
    slot1 = And(start_minutes >= 570, start_minutes + 30 <= 630)  # 9:30-10:30
    slot2 = And(start_minutes >= 690, start_minutes + 30 <= 750)  # 11:30-12:30
    slot3 = And(start_minutes >= 810, start_minutes + 30 <= 870)  # 13:30-14:30
    slot4 = And(start_minutes >= 930, start_minutes + 30 <= 960)  # 15:30-16:00
    tuesday_constraint = And(d == 1, Or(slot1, slot2, slot3, slot4))
    
    s.add(If(d == 0, monday_constraint, tuesday_constraint))
    
    cost = If(d == 0, 1, 0)
    cost = cost + If(And(d == 1, start_minutes < 870), 1, 0)
    s.minimize(cost)
    
    if s.check() == sat:
        m = s.model()
        day_val = m[d].as_long()
        start_val = m[start_minutes].as_long()
        
        day_str = "Monday" if day_val == 0 else "Tuesday"
        
        start_hour = start_val // 60
        start_min = start_val % 60
        start_time = f"{start_hour:02d}:{start_min:02d}"
        
        end_val = start_val + 30
        end_hour = end_val // 60
        end_min = end_val % 60
        end_time = f"{end_hour:02d}:{end_min:02d}"
        
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()