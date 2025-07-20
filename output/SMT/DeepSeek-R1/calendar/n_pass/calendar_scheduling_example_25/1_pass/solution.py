from z3 import *

def main():
    # Initialize the solver
    s = Int('s')
    solver = Solver()
    
    # Convert all times to minutes from 9:00 (9:00 is 0 minutes, 17:00 is 480 minutes)
    work_start = 0      # 9:00
    work_end = 480      # 17:00
    meeting_duration = 60
    
    # Constraints: start time must be within work hours and meeting must end by work_end
    solver.add(s >= work_start)
    solver.add(s + meeting_duration <= work_end)  # s <= 420
    
    # Busy intervals in minutes (start inclusive, end exclusive)
    intervals = [
        # Anthony's busy intervals
        (30, 60),      # 9:30-10:00
        (180, 240),    # 12:00-13:00
        (420, 450),    # 16:00-16:30
        
        # Pamela's busy intervals
        (30, 60),      # 9:30-10:00 (same as Anthony's first)
        (450, 480),    # 16:30-17:00
        
        # Zachary's busy intervals
        (0, 150),      # 9:00-11:30
        (180, 210),    # 12:00-12:30
        (240, 270),    # 13:00-13:30
        (330, 360),    # 14:30-15:00
        (420, 480)     # 16:00-17:00
    ]
    
    # Add constraint for Pamela's preference: meeting must end by 14:30 (330 minutes)
    solver.add(s + meeting_duration <= 330)  # s <= 270
    
    # Add constraints to avoid all busy intervals
    for (a, b) in intervals:
        solver.add(Or(s >= b, s + meeting_duration <= a))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model.eval(s).as_long()
        
        # Convert start_minutes to time format
        hours = start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{9 + hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = start_minutes + meeting_duration
        end_hours = end_minutes // 60
        end_minutes_remainder = end_minutes % 60
        end_time = f"{9 + end_hours:02d}:{end_minutes_remainder:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()