from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Convert all times to minutes since 9:00 (540 minutes from midnight)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30
    
    # Define the start time variable (in minutes since 9:00)
    start_time = Int('start_time')
    
    # Constraints: start_time must be within work hours and leave room for the meeting
    s.add(start_time >= work_start)
    s.add(start_time + meeting_duration <= work_end)
    
    # Each participant's busy times in minutes since midnight (or 9:00)
    # Steven: free all day
    # Roy: free all day
    
    # Cynthia's busy slots:
    # 9:30-10:30, 11:30-12:00, 13:00-13:30, 15:00-16:00
    cynthia_busy = [
        (9*60 + 30, 10*60 + 30),
        (11*60 + 30, 12*60),
        (13*60, 13*60 + 30),
        (15*60, 16*60)
    ]
    
    # Lauren's busy slots:
    # 9:00-9:30, 10:30-11:00, 11:30-12:00, 13:00-13:30, 14:00-14:30, 15:00-15:30, 16:00-17:00
    lauren_busy = [
        (9*60, 9*60 + 30),
        (10*60 + 30, 11*60),
        (11*60 + 30, 12*60),
        (13*60, 13*60 + 30),
        (14*60, 14*60 + 30),
        (15*60, 15*60 + 30),
        (16*60, 17*60)
    ]
    
    # Robert's busy slots:
    # 10:30-11:00, 11:30-12:00, 12:30-13:30, 14:00-16:00
    robert_busy = [
        (10*60 + 30, 11*60),
        (11*60 + 30, 12*60),
        (12*60 + 30, 13*60 + 30),
        (14*60, 16*60)
    ]
    
    # Function to add constraints that the meeting does not overlap with any busy slot
    def add_no_overlap_constraints(busy_slots):
        for (busy_start, busy_end) in busy_slots:
            # The meeting must be either entirely before or entirely after the busy slot
            s.add(Or(
                start_time + meeting_duration <= busy_start,
                start_time >= busy_end
            ))
    
    # Add constraints for each participant's busy slots
    add_no_overlap_constraints(cynthia_busy)
    add_no_overlap_constraints(lauren_busy)
    add_no_overlap_constraints(robert_busy)
    
    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        earliest_start = m.evaluate(start_time).as_long()
        
        # Convert start and end times back to HH:MM format
        start_hh = earliest_start // 60
        start_mm = earliest_start % 60
        end_time_min = earliest_start + meeting_duration
        end_hh = end_time_min // 60
        end_mm = end_time_min % 60
        
        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
        print(f"End Time: {end_hh:02d}:{end_mm:02d}")
    else:
        print("No solution found")

solve_scheduling()