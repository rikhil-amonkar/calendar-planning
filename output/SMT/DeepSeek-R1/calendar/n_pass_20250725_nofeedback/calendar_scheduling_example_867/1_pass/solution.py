from z3 import *

def main():
    # Define busy intervals in minutes from 9:00
    Betty_busy = [
        [(0, 30), (150, 180), (210, 240), (270, 300), (450, 480)],   # Tuesday
        [(30, 90), (240, 270), (300, 330)],                           # Wednesday
        [(30, 60), (150, 180), (300, 330), (360, 390), (450, 480)]    # Thursday
    ]
    
    Scott_busy = [
        [(0, 30), (60, 120), (150, 180), (210, 270), (300, 360), (420, 450)],   # Tuesday
        [(30, 210), (240, 270), (300, 330), (360, 390), (420, 450)],            # Wednesday
        [(0, 30), (60, 90), (120, 180), (210, 240), (360, 420), (450, 480)]     # Thursday
    ]
    
    day = Int('day')
    start = Int('start')
    
    # Model 1: Try without Wednesday (Tuesday or Thursday)
    s1 = Solver()
    s1.add(Or(day == 0, day == 2))  # Tuesday or Thursday
    s1.add(start >= 0, start <= 450)  # Meeting must end by 17:00 (480 minutes)
    s1.add(Implies(Or(day == 0, day == 2), start >= 360))  # After 15:00 on Tue/Thu
    
    # Add non-overlap constraints for Betty and Scott for Tuesday and Thursday
    for d in [0, 2]:
        for (s_int, e_int) in Betty_busy[d]:
            s1.add(Implies(day == d, Or(start + 30 <= s_int, start >= e_int)))
        for (s_int, e_int) in Scott_busy[d]:
            s1.add(Implies(day == d, Or(start + 30 <= s_int, start >= e_int)))
    
    if s1.check() == sat:
        m = s1.model()
        d_val = m[day].as_long()
        s_val = m[start].as_long()
    else:
        # Model 2: Include Wednesday
        s2 = Solver()
        s2.add(Or(day == 0, day == 1, day == 2))  # Tuesday, Wednesday, or Thursday
        s2.add(start >= 0, start <= 450)
        s2.add(Implies(Or(day == 0, day == 2), start >= 360))  # After 15:00 on Tue/Thu
        
        # Add non-overlap constraints for all days
        for d in [0, 1, 2]:
            for (s_int, e_int) in Betty_busy[d]:
                s2.add(Implies(day == d, Or(start + 30 <= s_int, start >= e_int)))
            for (s_int, e_int) in Scott_busy[d]:
                s2.add(Implies(day == d, Or(start + 30 <= s_int, start >= e_int)))
        
        if s2.check() == sat:
            m = s2.model()
            d_val = m[day].as_long()
            s_val = m[start].as_long()
        else:
            print("SOLUTION:\nDay: \nStart Time: \nEnd Time: ")
            return
    
    # Convert day value to string
    days = ["Tuesday", "Wednesday", "Thursday"]
    day_str = days[d_val]
    
    # Convert start time to HH:MM
    total_minutes = s_val
    hours = 9 + total_minutes // 60
    minutes = total_minutes % 60
    start_time = f"{hours}:{minutes:02d}"
    
    # Calculate end time (start time + 30 minutes)
    end_minutes = s_val + 30
    end_hours = 9 + end_minutes // 60
    end_minutes %= 60
    end_time = f"{end_hours}:{end_minutes:02d}"
    
    # Output the solution
    print("SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")

if __name__ == "__main__":
    main()