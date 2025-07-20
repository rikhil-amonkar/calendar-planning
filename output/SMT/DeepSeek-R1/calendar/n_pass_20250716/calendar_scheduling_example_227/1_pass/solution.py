from z3 import *

def main():
    # Busy intervals in minutes from 9:00 (each interval is [start, end])
    david_busy = [[150, 180], [330, 360]]          # 11:30-12:00, 14:30-15:00
    douglas_busy = [[30, 60], [150, 180], [240, 270], [330, 360]]  # 9:30-10:00, 11:30-12:00, 13:00-13:30, 14:30-15:00
    ralph_busy = [[0, 30], [60, 120], [150, 210], [270, 360], [390, 420], [450, 480]]  # 9:00-9:30, 10:00-11:00, 11:30-12:30, 13:30-15:00, 15:30-16:00, 16:30-17:00
    jordan_busy = [[0, 60], [180, 210], [240, 270], [330, 360], [390, 480]]  # 9:00-10:00, 12:00-12:30, 13:00-13:30, 14:30-15:00, 15:30-17:00
    
    # Initialize Z3 solver and integer variable for start time
    s = Int('s')
    solver = Solver()
    
    # Constraints: meeting within work hours (9:00-17:00) and David's preference (start >= 14:00)
    solver.add(s >= 300)  # 14:00 is 300 minutes from 9:00
    solver.add(s <= 450)  # Meeting must end by 17:00 (30 minutes before 480 minutes)
    
    # Add constraints for each participant's busy intervals
    for start_busy, end_busy in david_busy:
        solver.add(Or(s + 30 <= start_busy, s >= end_busy))
    
    for start_busy, end_busy in douglas_busy:
        solver.add(Or(s + 30 <= start_busy, s >= end_busy))
    
    for start_busy, end_busy in ralph_busy:
        solver.add(Or(s + 30 <= start_busy, s >= end_busy))
    
    for start_busy, end_busy in jordan_busy:
        solver.add(Or(s + 30 <= start_busy, s >= end_busy))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        start_val = model[s].as_long()
        
        # Convert start time to "HH:MM" format
        start_hour = 9 + start_val // 60
        start_minute = start_val % 60
        start_time = f"{start_hour}:{start_minute:02d}"
        
        # Calculate end time (30 minutes later)
        end_val = start_val + 30
        end_hour = 9 + end_val // 60
        end_minute = end_val % 60
        end_time = f"{end_hour}:{end_minute:02d}"
        
        # Output the meeting details
        print("Monday")
        print(start_time)
        print(end_time)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()