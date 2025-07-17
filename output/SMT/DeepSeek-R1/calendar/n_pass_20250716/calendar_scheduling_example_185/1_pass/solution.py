from z3 import *

def main():
    # Initialize the solver
    s = Int('s')
    solver = Solver()
    
    # Meeting must be between 9:00 and 17:00, duration 30 minutes.
    # Also, Megan's preference: avoid before 10:00, so start at or after 10:00 (60 minutes from 9:00).
    solver.add(s >= 60)
    solver.add(s <= 450)  # because 450 + 30 = 480 (17:00)
    
    # Define busy intervals for each participant in minutes from 9:00 (start inclusive, end exclusive)
    kimberly_busy = [(60, 90), (120, 180), (420, 450)]
    marie_busy = [(60, 120), (150, 360), (420, 450)]
    diana_busy = [(30, 60), (90, 330), (390, 480)]
    
    # Add constraints for Kimberly
    for (b_start, b_end) in kimberly_busy:
        solver.add(Or(s + 30 <= b_start, s >= b_end))
    
    # Add constraints for Marie
    for (b_start, b_end) in marie_busy:
        solver.add(Or(s + 30 <= b_start, s >= b_end))
    
    # Add constraints for Diana
    for (b_start, b_end) in diana_busy:
        solver.add(Or(s + 30 <= b_start, s >= b_end))
    
    # Check for a solution
    if solver.check() == sat:
        m = solver.model()
        start_minutes = m[s].as_long()
        
        # Convert start_minutes back to time string
        total_minutes_from_midnight_start = 9 * 60 + start_minutes
        hours_start = total_minutes_from_midnight_start // 60
        minutes_start = total_minutes_from_midnight_start % 60
        start_time = f"{hours_start}:{minutes_start:02d}"
        
        end_minutes = start_minutes + 30
        total_minutes_from_midnight_end = 9 * 60 + end_minutes
        hours_end = total_minutes_from_midnight_end // 60
        minutes_end = total_minutes_from_midnight_end % 60
        end_time = f"{hours_end}:{minutes_end:02d}"
        
        # Output the meeting time
        print("Monday", start_time, end_time)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()