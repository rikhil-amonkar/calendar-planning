from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define time in minutes from Monday 9:00
    # Monday: 0 to 480 (9:00 to 17:00)
    # Tuesday: 480 to 960 (9:00 to 17:00)
    start = Int('start')
    meeting_duration = 60
    
    # Constraint: Meeting must start and end within work hours on Monday or Tuesday
    s.add(Or(
        And(start >= 0, start + meeting_duration <= 480),   # Monday
        And(start >= 480, start + meeting_duration <= 960)  # Tuesday
    ))
    
    # Patricia's busy intervals in minutes from Monday 9:00
    patricia_busy = [
        (60, 90),    # Mon 10:00-10:30
        (150, 180),  # Mon 11:30-12:00
        (240, 270),  # Mon 13:00-13:30
        (330, 390),  # Mon 14:30-15:30
        (420, 450),  # Mon 16:00-16:30
        (540, 570),  # Tue 10:00-10:30
        (600, 660),  # Tue 11:00-12:00
        (780, 840),  # Tue 14:00-16:00
        (930, 960)   # Tue 16:30-17:00
    ]
    
    # Jesse's busy intervals
    jesse_busy = [
        (0, 480),    # Mon 9:00-17:00 (entire day)
        (600, 630),  # Tue 11:00-11:30
        (660, 690),  # Tue 12:00-12:30
        (720, 780),  # Tue 13:00-14:00
        (810, 840),  # Tue 14:30-15:00
        (870, 960)   # Tue 15:30-17:00
    ]
    
    # Add constraints for Patricia
    for busy_start, busy_end in patricia_busy:
        s.add(Or(
            start + meeting_duration <= busy_start,
            start >= busy_end
        ))
    
    # Add constraints for Jesse
    for busy_start, busy_end in jesse_busy:
        s.add(Or(
            start + meeting_duration <= busy_start,
            start >= busy_end
        ))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_val = m.evaluate(start).as_long()
        
        # Determine day and time
        if start_val < 480:
            day = "Monday"
            base_time = start_val
        else:
            day = "Tuesday"
            base_time = start_val - 480
        
        # Convert minutes to HH:MM format
        hours = base_time // 60
        minutes = base_time % 60
        start_str = f"{9 + hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_time = start_val + meeting_duration
        if end_time < 480:
            end_base = end_time
        else:
            end_base = end_time - 480
        end_hours = end_base // 60
        end_minutes = end_base % 60
        end_str = f"{9 + end_hours:02d}:{end_minutes:02d}"
        
        print(f"{day} {start_str}:{end_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()