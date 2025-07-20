from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define variables: day (0=Monday, 1=Tuesday) and start time in minutes from 9:00
    day = Int('day')
    start = Int('start')
    
    # Day must be 0 or 1
    s.add(Or(day == 0, day == 1))
    # Start time must be between 0 and 420 (inclusive) to allow a 60-minute meeting ending by 480 (17:00)
    s.add(start >= 0, start <= 420)
    
    # Blocked intervals in minutes from 9:00
    # Monday blocks
    gary_monday = [(30, 60), (120, 240), (300, 330), (450, 480)]
    david_monday = [(0, 30), (60, 240), (330, 450)]
    monday_blocks = gary_monday + david_monday
    
    # Tuesday blocks
    gary_tuesday = [(0, 30), (90, 120), (330, 420)]
    david_tuesday = [(0, 30), (60, 90), (120, 210), (240, 330), (360, 420), (450, 480)]
    tuesday_blocks = gary_tuesday + david_tuesday
    
    # Constraints for Monday: if day is 0, the meeting must avoid all Monday blocks
    monday_constraints = []
    for (a, b) in monday_blocks:
        # The meeting [start, start+60) must not overlap [a, b): so either ends before a or starts after b
        monday_constraints.append(Or(start + 60 <= a, start >= b))
    
    # Constraints for Tuesday: if day is 1, the meeting must avoid all Tuesday blocks
    tuesday_constraints = []
    for (a, b) in tuesday_blocks:
        tuesday_constraints.append(Or(start + 60 <= a, start >= b))
    
    # Add constraints based on the chosen day
    s.add(Or(
        And(day == 0, *monday_constraints),
        And(day == 1, *tuesday_constraints)
    ))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        d_val = m[day].as_long()
        start_val = m[start].as_long()
        
        # Convert start time to time string
        total_minutes_start = start_val
        start_hour = 9 + total_minutes_start // 60
        start_minute = total_minutes_start % 60
        start_time = f"{start_hour}:{start_minute:02d}"
        
        # Calculate end time
        total_minutes_end = total_minutes_start + 60
        end_hour = 9 + total_minutes_end // 60
        end_minute = total_minutes_end % 60
        end_time = f"{end_hour}:{end_minute:02d}"
        
        day_str = "Monday" if d_val == 0 else "Tuesday"
        print(f"{day_str} {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()