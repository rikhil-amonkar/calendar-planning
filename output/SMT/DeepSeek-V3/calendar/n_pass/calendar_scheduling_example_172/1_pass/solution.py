from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Define the start time in minutes from 9:00 (0 minutes is 9:00)
    start_time = Int('start_time')
    
    # Meeting duration is 30 minutes
    duration = 30
    end_time = start_time + duration
    
    # Total working hours: 9:00 to 17:00 is 8 hours = 480 minutes
    max_time = 480
    
    # Constraint: start_time must be >= 0 and end_time <= 480
    s.add(start_time >= 0)
    s.add(end_time <= max_time)
    
    # Define each person's busy slots in minutes from 9:00
    # Patrick's busy slots
    patrick_busy = [
        (0, 30),    # 9:00-9:30
        (60, 90),   # 10:00-10:30
        (270, 300), # 13:30-14:00
        (420, 450)  # 16:00-16:30
    ]
    
    # Kayla's busy slots
    kayla_busy = [
        (210, 270), # 12:30-13:30
        (360, 390), # 15:00-15:30
        (420, 450)  # 16:00-16:30
    ]
    
    # Carl's busy slots
    carl_busy = [
        (90, 120),  # 10:30-11:00
        (180, 210), # 12:00-12:30
        (240, 270), # 13:00-13:30
        (330, 480)  # 14:30-17:00
    ]
    
    # Christian's busy slots
    christian_busy = [
        (0, 210),   # 9:00-12:30
        (240, 300), # 13:00-14:00
        (330, 480)  # 14:30-17:00
    ]
    
    # Function to add no-overlap constraints for a person's busy slots
    def add_no_overlap_constraints(busy_slots):
        for (busy_start, busy_end) in busy_slots:
            # The meeting must be entirely before the busy slot or entirely after
            s.add(Or(end_time <= busy_start, start_time >= busy_end))
    
    # Add constraints for each person
    add_no_overlap_constraints(patrick_busy)
    add_no_overlap_constraints(kayla_busy)
    add_no_overlap_constraints(carl_busy)
    add_no_overlap_constraints(christian_busy)
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_min = model[start_time].as_long()
        
        # Calculate start and end times in HH:MM format
        start_hh = 9 + start_min // 60
        start_mm = start_min % 60
        end_min = start_min + duration
        end_hh = 9 + end_min // 60
        end_mm = end_min % 60
        
        # Format as two-digit strings
        start_time_str = f"{start_hh:02d}:{start_mm:02d}"
        end_time_str = f"{end_hh:02d}:{end_mm:02d}"
        
        # Print the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()