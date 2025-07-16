from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Define the start time variable in minutes from 9:00 (0 represents 9:00)
    start_time = Int('start_time')
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Total working hours: 9:00 to 17:00 is 8 hours = 480 minutes
    max_time = 480 - duration  # Latest possible start time is 16:30
    
    # Constraint: start_time must be >= 0 and <= max_time (16:30)
    s.add(start_time >= 0)
    s.add(start_time <= max_time)
    
    # Each participant's busy intervals in minutes from 9:00
    # Eric has no meetings, so no constraints
    
    # Ashley's busy intervals:
    ashley_busy = [(60, 90), (120, 180), (150, 210), (360, 420)]
    # Ronald's busy intervals:
    ronald_busy = [(0, 30), (60, 150), (150, 300), (330, 480)]
    # Larry's busy intervals:
    larry_busy = [(0, 180), (240, 480)]
    
    # Function to add no-overlap constraints for a participant's busy intervals
    def add_no_overlap_constraints(busy_intervals):
        for (busy_start, busy_end) in busy_intervals:
            # The meeting must not overlap with this busy interval
            # So either meeting ends before busy_start or starts after busy_end
            s.add(Or(
                start_time + duration <= busy_start,
                start_time >= busy_end
            ))
    
    # Add constraints for each participant
    add_no_overlap_constraints(ashley_busy)
    add_no_overlap_constraints(ronald_busy)
    add_no_overlap_constraints(larry_busy)
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_minutes = model[start_time].as_long()
        
        # Calculate start and end times in HH:MM format
        start_hh = 9 + start_minutes // 60
        start_mm = start_minutes % 60
        end_minutes = start_minutes + duration
        end_hh = 9 + end_minutes // 60
        end_mm = end_minutes % 60
        
        # Format the times as two-digit strings
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