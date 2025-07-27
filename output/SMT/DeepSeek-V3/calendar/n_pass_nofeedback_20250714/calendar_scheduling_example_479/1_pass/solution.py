from z3 import *

def solve_meeting_schedule():
    # Initialize the solver
    s = Solver()
    
    # Work hours are 9:00 to 17:00 (9 AM to 5 PM), which is 0 to 480 minutes (since 9 AM is 0)
    work_start = 0
    work_end = 480  # 17:00 is 8 hours after 9:00, 8*60=480
    
    # Meeting duration is 1 hour (60 minutes)
    duration = 60
    
    # Define the start time of the meeting in minutes since 9:00
    start_time = Int('start_time')
    
    # Constraint: start_time must be within work hours and leave room for the duration
    s.add(start_time >= work_start)
    s.add(start_time + duration <= work_end)
    
    # Define each participant's busy times in minutes since 9:00
    # Each busy time is a list of (start, end) intervals
    
    # Joshua's busy times: 11:00-12:30, 13:30-14:30, 16:30-17:00
    joshua_busy = [(120, 150), (210, 270), (390, 480)]
    
    # Jerry's busy times: 9:00-9:30, 10:30-12:00, 12:30-13:00, 13:30-14:00, 14:30-15:00, 15:30-16:00
    jerry_busy = [(0, 30), (90, 180), (210, 240), (270, 300), (330, 360)]
    
    # Jesse's busy times: 9:00-9:30, 10:30-12:00, 12:30-13:00, 14:30-15:00, 15:30-16:30
    jesse_busy = [(0, 30), (90, 180), (210, 240), (330, 360), (390, 450)]
    
    # Kenneth's busy times: 10:30-12:30, 13:30-14:00, 14:30-15:00, 15:30-16:00, 16:30-17:00
    kenneth_busy = [(90, 210), (210, 240), (330, 360), (390, 420), (450, 480)]
    
    # Evelyn, Kevin, Gerald are free all day, so no constraints
    
    # Function to add constraints that the meeting does not overlap with any busy intervals
    def add_no_overlap_constraints(busy_intervals):
        for (busy_start, busy_end) in busy_intervals:
            # The meeting is either entirely before or entirely after the busy interval
            s.add(Or(
                start_time + duration <= busy_start,
                start_time >= busy_end
            ))
    
    # Add constraints for each busy participant
    add_no_overlap_constraints(joshua_busy)
    add_no_overlap_constraints(jerry_busy)
    add_no_overlap_constraints(jesse_busy)
    add_no_overlap_constraints(kenneth_busy)
    
    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        start = model[start_time].as_long()
        
        # Convert start time back to HH:MM format
        meeting_start_hh = 9 + start // 60
        meeting_start_mm = start % 60
        start_time_str = f"{meeting_start_hh:02d}:{meeting_start_mm:02d}"
        
        meeting_end_hh = 9 + (start + duration) // 60
        meeting_end_mm = (start + duration) % 60
        end_time_str = f"{meeting_end_hh:02d}:{meeting_end_mm:02d}"
        
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_meeting_schedule()