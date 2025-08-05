from z3 import *

def main():
    # Convert all times to minutes from 9:00
    # Busy intervals for each participant
    busy_intervals = [
        # Jeffrey's meetings
        (30, 60),    # 9:30-10:00
        (90, 120),   # 10:30-11:00
        # Virginia's meetings
        (0, 30),     # 9:00-9:30
        (60, 90),    # 10:00-10:30
        (330, 360),  # 14:30-15:00
        (420, 450),  # 16:00-16:30
        # Melissa's meetings
        (0, 150),    # 9:00-11:30
        (180, 210),  # 12:00-12:30
        (240, 360),  # 13:00-15:00
        (420, 480)   # 16:00-17:00
    ]
    
    s = Int('s')
    solver = Solver()
    
    # Constraint: meeting must be within work hours (9:00 to 17:00)
    solver.add(s >= 0)
    solver.add(s <= 450)  # 17:00 is 480 minutes; 480 - 30 = 450
    
    # Constraints to avoid busy intervals
    for (b_start, b_end) in busy_intervals:
        solver.add(Or(s + 30 <= b_start, s >= b_end))
    
    # Try to satisfy Melissa's preference: meeting ends by 14:00 (300 minutes from 9:00)
    solver.push()
    solver.add(s + 30 <= 300)
    
    if solver.check() == sat:
        m = solver.model()
        start_minutes = m[s].as_long()
    else:
        solver.pop()
        if solver.check() == sat:
            m = solver.model()
            start_minutes = m[s].as_long()
        else:
            # According to the problem, there must be a solution
            print("No solution found")
            return
    
    # Convert start_minutes back to time
    total_minutes_start = start_minutes
    start_hour = 9 + total_minutes_start // 60
    start_min = total_minutes_start % 60
    start_time_str = f"{start_hour:02d}:{start_min:02d}"
    
    total_minutes_end = start_minutes + 30
    end_hour = 9 + total_minutes_end // 60
    end_min = total_minutes_end % 60
    end_time_str = f"{end_hour:02d}:{end_min:02d}"
    
    # Output the solution
    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {start_time_str}")
    print(f"End Time: {end_time_str}")

if __name__ == "__main__":
    main()