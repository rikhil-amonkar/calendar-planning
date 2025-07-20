from z3 import *

def main():
    # Initialize the solver
    s = Solver()
    
    # Define the start time in minutes from 9:00
    start = Int('start')
    
    # Meeting duration in minutes
    duration = 60
    
    # Total available time (9:00 to 17:00 is 8 hours = 480 minutes)
    total_minutes = 480
    
    # Constraints: start must be within [0, total_minutes - duration]
    s.add(start >= 0)
    s.add(start <= total_minutes - duration)
    
    # Define busy intervals for each participant as half-open [start_minute, end_minute)
    # Julie's busy intervals
    julie_busy = [
        (0, 30),      # 9:00-9:30
        (120, 150),    # 11:00-11:30
        (180, 210),    # 12:00-12:30
        (270, 300),    # 13:30-14:00
        (420, 480)     # 16:00-17:00
    ]
    
    # Sean's busy intervals
    sean_busy = [
        (0, 30),      # 9:00-9:30
        (240, 270),    # 13:00-13:30
        (360, 390),    # 15:00-15:30
        (420, 450)     # 16:00-16:30
    ]
    
    # Lori's busy intervals
    lori_busy = [
        (60, 90),      # 10:00-10:30
        (120, 240),    # 11:00-13:00
        (390, 480)     # 15:30-17:00
    ]
    
    # Add constraints for Julie
    for (busy_start, busy_end) in julie_busy:
        s.add(Or(start + duration <= busy_start, start >= busy_end))
    
    # Add constraints for Sean
    for (busy_start, busy_end) in sean_busy:
        s.add(Or(start + duration <= busy_start, start >= busy_end))
    
    # Add constraints for Lori
    for (busy_start, busy_end) in lori_busy:
        s.add(Or(start + duration <= busy_start, start >= busy_end))
    
    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        start_minutes = model[start].as_long()
        
        # Convert start_minutes back to time string
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = start_minutes + duration
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()