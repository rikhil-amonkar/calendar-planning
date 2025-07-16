from z3 import *

def solve_meeting_scheduling():
    # Initialize the solver
    solver = Solver()
    
    # Define the start time variable in minutes from 9:00 (0 minutes is 9:00)
    start_time = Int('start_time')
    duration = 30  # meeting duration in minutes
    
    # Total working hours: 9:00 to 17:00 is 8 hours = 480 minutes
    max_time = 480
    
    # Constraint: start_time must be >= 0 (9:00) and end_time <= 480 (17:00)
    end_time = start_time + duration
    solver.add(start_time >= 0)
    solver.add(end_time <= max_time)
    
    # Define each participant's busy slots in minutes from 9:00
    # Lisa's busy slots
    lisa_busy = [
        (0, 60),      # 9:00-10:00
        (90, 150),     # 10:30-11:30
        (210, 240),    # 12:30-13:00
        (420, 450)     # 16:00-16:30
    ]
    
    # Bobby's busy slots
    bobby_busy = [
        (0, 30),       # 9:00-9:30
        (60, 90),       # 10:00-10:30
        (150, 180),     # 11:30-12:00
        (360, 390)      # 15:00-15:30
    ]
    # Bobby's preference: meeting should end by 15:00 (360 minutes)
    solver.add(end_time <= 360)
    
    # Randy's busy slots
    randy_busy = [
        (30, 60),      # 9:30-10:00
        (90, 120),     # 10:30-11:00
        (150, 210),    # 11:30-12:30
        (240, 270),    # 13:00-13:30
        (330, 390),    # 14:30-15:30
        (420, 450)     # 16:00-16:30
    ]
    
    # Function to add no overlap constraints for a participant's busy slots
    def add_no_overlap_constraints(busy_slots):
        for (busy_start, busy_end) in busy_slots:
            # The meeting must not overlap with this busy slot
            solver.add(Or(
                end_time <= busy_start,
                start_time >= busy_end
            ))
    
    # Add constraints for each participant
    add_no_overlap_constraints(lisa_busy)
    add_no_overlap_constraints(bobby_busy)
    add_no_overlap_constraints(randy_busy)
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        start_min = model[start_time].as_long()
        
        # Convert start_min back to HH:MM format
        start_hour = 9 + start_min // 60
        start_minute = start_min % 60
        end_min = start_min + duration
        end_hour = 9 + end_min // 60
        end_minute = end_min % 60
        
        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hour:02d}:{start_minute:02d}")
        print(f"End Time: {end_hour:02d}:{end_minute:02d}")
    else:
        print("No solution found")

solve_meeting_scheduling()