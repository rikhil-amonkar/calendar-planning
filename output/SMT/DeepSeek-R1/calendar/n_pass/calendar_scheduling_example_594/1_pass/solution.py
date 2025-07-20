from z3 import *

def main():
    # Convert time to minutes from 9:00
    # Adam's busy intervals
    adam_busy = [
        (30, 60),    # 9:30-10:00
        (210, 240),  # 12:30-13:00
        (330, 360),  # 14:30-15:00
        (450, 480)   # 16:30-17:00
    ]
    
    # Roy's busy intervals
    roy_busy = [
        (60, 120),   # 10:00-11:00
        (150, 240),  # 11:30-13:00
        (270, 330),  # 13:30-14:30
        (450, 480)   # 16:30-17:00
    ]
    
    # Initialize Z3 solver with optimization
    s = Optimize()
    start = Int('start')
    
    # Meeting must be within 9:00 to 17:00 and last 30 minutes
    s.add(start >= 0)
    s.add(start + 30 <= 480)  # 17:00 is 480 minutes from 9:00
    
    # Add constraints for Adam's busy intervals
    for (busy_start, busy_end) in adam_busy:
        s.add(Or(start + 30 <= busy_start, start >= busy_end))
    
    # Add constraints for Roy's busy intervals
    for (busy_start, busy_end) in roy_busy:
        s.add(Or(start + 30 <= busy_start, start >= busy_end))
    
    # Minimize the start time to find the earliest slot
    s.minimize(start)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_minutes = m[start].as_long()
        
        # Convert start time back to HH:MM format
        total_minutes = start_minutes
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = start_minutes + 30
        hours_end = 9 + end_minutes // 60
        minutes_end = end_minutes % 60
        end_time = f"{hours_end:02d}:{minutes_end:02d}"
        
        # Output the solution in the required format
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()