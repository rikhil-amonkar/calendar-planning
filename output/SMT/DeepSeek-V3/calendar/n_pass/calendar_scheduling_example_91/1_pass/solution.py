from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    solver = Solver()
    
    # Define the start time in minutes from 9:00 (540 minutes from midnight)
    start_time = Int('start_time')
    
    # Meeting duration is 60 minutes
    duration = 60
    
    # Total working hours: 9:00 to 17:00 is 8 hours = 480 minutes
    max_time = 480
    
    # Constraint: start_time must be >= 0 (9:00 is 0 minutes from start) and <= max_time - duration (16:00)
    solver.add(start_time >= 0)
    solver.add(start_time <= max_time - duration)
    
    # Define each participant's busy intervals in minutes from 9:00
    # Danielle's busy intervals: 9:00-10:00 (0-60), 10:30-11:00 (90-120), 14:30-15:00 (330-360), 15:30-16:00 (390-420), 16:30-17:00 (450-480)
    danielle_busy = [(0, 60), (90, 120), (330, 360), (390, 420), (450, 480)]
    
    # Bruce's busy intervals: 11:00-11:30 (120-150), 12:30-13:00 (210-240), 14:00-14:30 (300-330), 15:30-16:00 (390-420)
    bruce_busy = [(120, 150), (210, 240), (300, 330), (390, 420)]
    
    # Eric's busy intervals: 9:00-9:30 (0-30), 10:00-11:00 (60-120), 11:30-13:00 (150-240), 14:30-15:30 (330-390)
    eric_busy = [(0, 30), (60, 120), (150, 240), (330, 390)]
    
    # Function to add no-overlap constraints for a participant's busy intervals
    def add_no_overlap_constraints(busy_intervals):
        for (busy_start, busy_end) in busy_intervals:
            # The meeting must not overlap with this busy interval
            # So either meeting ends before busy starts or starts after busy ends
            solver.add(Or(start_time + duration <= busy_start, start_time >= busy_end))
    
    # Add constraints for each participant
    add_no_overlap_constraints(danielle_busy)
    add_no_overlap_constraints(bruce_busy)
    add_no_overlap_constraints(eric_busy)
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model.eval(start_time).as_long()
        
        # Convert start_minutes back to HH:MM format
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        end_minutes = start_minutes + duration
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hour:02d}:{start_minute:02d}")
        print(f"End Time: {end_hour:02d}:{end_minute:02d}")
    else:
        print("No solution found")

solve_scheduling()