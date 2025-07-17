from z3 import *

def main():
    # Create solver
    s_solver = Solver()
    
    # Variables
    day = Int('day')
    s = Int('s')  # start time in minutes after 9:00
    
    # Day must be 0 (Monday) or 1 (Tuesday)
    s_solver.add(Or(day == 0, day == 1))
    # Start time must be within [0, 420] minutes (so meeting ends by 17:00)
    s_solver.add(s >= 0, s <= 420)
    
    # Busy intervals for Patricia on Monday: (start_minute, end_minute) from 9:00
    pat_mon = [
        (60, 90),    # 10:00-10:30
        (150, 180),  # 11:30-12:00
        (240, 270),  # 13:00-13:30
        (330, 390),  # 14:30-15:30
        (420, 450)   # 16:00-16:30
    ]
    # Busy intervals for Jesse on Monday
    jes_mon = [
        (0, 480)     # Entire day blocked (9:00-17:00)
    ]
    
    # Busy intervals for Patricia on Tuesday
    pat_tue = [
        (60, 90),    # 10:00-10:30
        (120, 180),  # 11:00-12:00
        (300, 420)   # 14:00-16:00
    ]
    # Busy intervals for Jesse on Tuesday
    jes_tue = [
        (120, 150),  # 11:00-11:30
        (180, 210),  # 12:00-12:30
        (240, 300),  # 13:00-14:00
        (330, 360),  # 14:30-15:00
        (390, 480)   # 15:30-17:00
    ]
    
    # Add constraints: for each day, if selected, avoid all busy intervals for both participants
    # For Monday
    for (b_start, b_end) in pat_mon:
        s_solver.add(Or(day != 0, Or(s + 60 <= b_start, s >= b_end)))
    for (b_start, b_end) in jes_mon:
        s_solver.add(Or(day != 0, Or(s + 60 <= b_start, s >= b_end)))
    
    # For Tuesday
    for (b_start, b_end) in pat_tue:
        s_solver.add(Or(day != 1, Or(s + 60 <= b_start, s >= b_end)))
    for (b_start, b_end) in jes_tue:
        s_solver.add(Or(day != 1, Or(s + 60 <= b_start, s >= b_end)))
    
    # Check for solution
    if s_solver.check() == sat:
        model = s_solver.model()
        d = model[day].as_long()
        start_minute = model[s].as_long()
        
        # Convert start_minute to time string
        hours = 9 + start_minute // 60
        minutes = start_minute % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time (start_minute + 60 minutes)
        end_minute = start_minute + 60
        end_hours = 9 + end_minute // 60
        end_minutes = end_minute % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        
        # Map day integer to string
        day_str = "Monday" if d == 0 else "Tuesday"
        
        print(f"Meeting scheduled on {day_str} from {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()