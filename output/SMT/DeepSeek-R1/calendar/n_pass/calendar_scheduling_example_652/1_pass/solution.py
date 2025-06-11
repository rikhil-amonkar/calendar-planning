from z3 import *

def main():
    # Create a solver instance
    s = Solver()
    
    # Define the start time in minutes from 9:00 on Tuesday
    start = Int('start')
    
    # Add constraints
    s.add(start >= 0)  # Meeting must start at or after 9:00
    s.add(start + 30 <= 450)  # Meeting must end by 16:30 (450 minutes from 9:00)
    
    # Jesse's constraints: avoid busy periods on Tuesday
    s.add(Or(start + 30 <= 240, start >= 270))  # Avoid 13:00-13:30 and 14:00-15:00? 
    s.add(Or(start + 30 <= 300, start >= 360))  # Avoid 14:00-15:00? 
    
    # Lawrence's constraints: avoid busy periods on Tuesday
    s.add(Or(start + 30 <= 150, start >= 210))  # Avoid 11:30-12:30
    s.add(Or(start + 30 <= 240, start >= 270))  # Avoid 13:00-13:30
    s.add(Or(start + 30 <= 330, start >= 360))  # Avoid 14:30-15:00
    s.add(Or(start + 30 <= 390, start >= 450))  # Avoid 15:30-16:30
    
    # Additional constraints from analysis
    s.add(start >= 90)  # Lawrence is busy from 9:30 to 10:30, so start must be at or after 10:30 (90 minutes)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_val = m[start].as_long()
        
        # Calculate start time in HH:MM
        total_minutes_start = start_val
        hour_start = 9 + total_minutes_start // 60
        minute_start = total_minutes_start % 60
        start_time = f"{hour_start}:{minute_start:02d}"
        
        # Calculate end time in HH:MM
        total_minutes_end = start_val + 30
        hour_end = 9 + total_minutes_end // 60
        minute_end = total_minutes_end % 60
        end_time = f"{hour_end}:{minute_end:02d}"
        
        # Output the solution
        print("Tuesday")
        print(start_time)
        print(end_time)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()