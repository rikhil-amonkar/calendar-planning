from z3 import Int, Solver, Or, And

def main():
    # Initialize solver
    s = Solver()
    
    # Define start time variable in minutes from 9:00 (0 minutes = 9:00)
    start_min = Int('start_min')
    meeting_duration = 30
    total_minutes = 480  # 9:00 to 17:00 is 8 hours = 480 minutes
    
    # Constraints: start time must be within work hours
    s.add(start_min >= 0)
    s.add(start_min <= total_minutes - meeting_duration)
    
    # Convert busy times to minutes from 9:00
    # Patrick's busy intervals
    patrick_busy = [
        (0, 30),    # 9:00-9:30
        (60, 90),   # 10:00-10:30
        (270, 300), # 13:30-14:00
        (420, 450)  # 16:00-16:30
    ]
    
    # Kayla's busy intervals
    kayla_busy = [
        (210, 270), # 12:30-13:30
        (360, 390), # 15:00-15:30
        (420, 450)  # 16:00-16:30
    ]
    
    # Carl's busy intervals
    carl_busy = [
        (90, 120),  # 10:30-11:00
        (180, 210), # 12:00-12:30
        (240, 270), # 13:00-13:30
        (330, 480)  # 14:30-17:00
    ]
    
    # Christian's busy intervals
    christian_busy = [
        (0, 210),   # 9:00-12:30
        (240, 300), # 13:00-14:00
        (330, 480)  # 14:30-17:00
    ]
    
    # Function to add no-overlap constraints for a set of intervals
    def add_no_overlap_constraints(busy_intervals):
        constraints = []
        for start, end in busy_intervals:
            # Meeting must not overlap with busy interval
            constraints.append(Or(
                start_min + meeting_duration <= start,
                start_min >= end
            ))
        s.add(And(constraints))
    
    # Add constraints for each participant
    add_no_overlap_constraints(patrick_busy)
    add_no_overlap_constraints(kayla_busy)
    add_no_overlap_constraints(carl_busy)
    add_no_overlap_constraints(christian_busy)
    
    # Check for solution
    if s.check().r == 1:  # SAT
        model = s.model()
        start_val = model[start_min].as_long()
        
        # Convert start time to HH:MM format
        start_hour = 9 + start_val // 60
        start_minute = start_val % 60
        end_time = start_val + meeting_duration
        end_hour = 9 + end_time // 60
        end_minute = end_time % 60
        
        # Format time strings
        start_str = f"{start_hour:02d}:{start_minute:02d}"
        end_str = f"{end_hour:02d}:{end_minute:02d}"
        
        print(f"{start_str}:{end_str}")
        print("Monday")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()