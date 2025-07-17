from z3 import *

def main():
    # Initialize the solver
    s = Solver()
    
    # Define the start time variable in minutes from 9:00
    start = Int('start')
    
    # Meeting duration is 30 minutes, so start must be between 0 and 450 (inclusive)
    s.add(start >= 0)
    s.add(start <= 450)
    
    # Gregory's busy intervals (in minutes from 9:00)
    gregory_busy = [(0, 60), (90, 150), (210, 240), (270, 300)]
    for s_busy, e_busy in gregory_busy:
        s.add(Or(start + 30 <= s_busy, start >= e_busy))
    
    # Christine's busy intervals
    christine_busy = [(0, 150), (270, 480)]
    for s_busy, e_busy in christine_busy:
        s.add(Or(start + 30 <= s_busy, start >= e_busy))
    
    # Vincent's busy intervals
    vincent_busy = [(0, 30), (90, 180), (210, 300), (330, 480)]
    for s_busy, e_busy in vincent_busy:
        s.add(Or(start + 30 <= s_busy, start >= e_busy))
    
    # Natalie has no busy intervals
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start_minutes = m[start].as_long()
        
        # Convert start time to HH:MM format
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = start_minutes + 30
        end_hours = 9 + end_minutes // 60
        end_minutes_part = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes_part:02d}"
        
        # Output the result
        print("Monday", start_time, end_time)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()