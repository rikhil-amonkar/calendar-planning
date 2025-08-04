from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Work hours are from 9:00 (540 minutes) to 17:00 (1020 minutes)
    start_work = 540  # 9:00 in minutes
    end_work = 1020    # 17:00 in minutes
    meeting_duration = 30
    
    # Define the start time variable (in minutes since midnight)
    start_time = Int('start_time')
    
    # Constraints for the meeting to be within work hours
    s.add(start_time >= start_work)
    s.add(start_time + meeting_duration <= end_work)
    
    # Harold's preference: meeting must end by 13:00 (780 minutes)
    s.add(start_time + meeting_duration <= 780)
    
    # Each participant's busy times in minutes since midnight
    # Jacqueline's busy times (9:00-9:30, 11:00-11:30, 12:30-13:00, 15:30-16:00)
    j_busy = [(540, 570), (660, 690), (750, 780), (930, 960)]
    # Harold's busy times (10:00-10:30, 13:00-13:30, 15:00-17:00)
    h_busy = [(600, 630), (780, 810), (900, 1020)]
    # Arthur's busy times (9:00-9:30, 10:00-12:30, 14:30-15:00, 15:30-17:00)
    a_busy = [(540, 570), (600, 750), (870, 900), (930, 1020)]
    # Kelly's busy times (9:00-9:30, 10:00-11:00, 11:30-12:30, 14:00-15:00, 15:30-16:00)
    k_busy = [(540, 570), (600, 660), (690, 750), (840, 900), (930, 960)]
    
    # Function to add constraints that the meeting does not overlap with any busy time
    def add_no_overlap_constraints(busy_times):
        for (busy_start, busy_end) in busy_times:
            s.add(Or(start_time >= busy_end, start_time + meeting_duration <= busy_start))
    
    # Add constraints for each participant
    add_no_overlap_constraints(j_busy)
    add_no_overlap_constraints(h_busy)
    add_no_overlap_constraints(a_busy)
    add_no_overlap_constraints(k_busy)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start = m[start_time].as_long()
        
        # Convert start time from minutes to HH:MM format
        hours = start // 60
        minutes = start % 60
        start_str = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end = start + meeting_duration
        end_hours = end // 60
        end_minutes = end % 60
        end_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        # Print the solution
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

solve_scheduling()