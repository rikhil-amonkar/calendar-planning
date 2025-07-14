from z3 import *

def solve_meeting_scheduling():
    # Create a solver instance
    s = Solver()
    
    # Define the start time as an integer (minutes from 9:00)
    start_time = Int('start_time')
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Work hours are 9:00 to 17:00 (480 minutes from 9:00)
    min_time = 0  # 9:00 in minutes (0 minutes after 9:00)
    max_time = 8 * 60  # 17:00 is 8 hours after 9:00 (480 minutes)
    
    # Constraint: start_time must be within work hours and leave room for the duration
    s.add(start_time >= min_time)
    s.add(start_time + duration <= max_time)
    
    # Define each participant's busy times in minutes from 9:00
    # Jacqueline's busy times: 9:00-9:30, 11:00-11:30, 12:30-13:00, 15:30-16:00
    j_busy = [(0, 30), (120, 150), (210, 240), (390, 420)]
    
    # Harold's busy times: 10:00-10:30, 13:00-13:30, 15:00-17:00
    h_busy = [(60, 90), (240, 270), (360, 480)]
    
    # Arthur's busy times: 9:00-9:30, 10:00-12:30, 14:30-15:00, 15:30-17:00
    a_busy = [(0, 30), (60, 210), (330, 360), (390, 480)]
    
    # Kelly's busy times: 9:00-9:30, 10:00-11:00, 11:30-12:30, 14:00-15:00, 15:30-16:00
    k_busy = [(0, 30), (60, 120), (150, 210), (300, 360), (390, 420)]
    
    # Harold's preference: meeting must end by 13:00 (240 minutes from 9:00)
    s.add(start_time + duration <= 240)
    
    # Function to add no-overlap constraints for each participant
    def add_no_overlap_constraints(busy_times):
        for (busy_start, busy_end) in busy_times:
            # The meeting does not overlap with this busy interval if:
            # meeting ends before busy starts OR meeting starts after busy ends
            s.add(Or(start_time + duration <= busy_start, start_time >= busy_end))
    
    # Add constraints for each participant
    add_no_overlap_constraints(j_busy)
    add_no_overlap_constraints(h_busy)
    add_no_overlap_constraints(a_busy)
    add_no_overlap_constraints(k_busy)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_minutes = m.evaluate(start_time).as_long()
        
        # Convert start_minutes back to HH:MM format
        start_hh = 9 + start_minutes // 60
        start_mm = start_minutes % 60
        end_minutes = start_minutes + duration
        end_hh = 9 + end_minutes // 60
        end_mm = end_minutes % 60
        
        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
        print(f"End Time: {end_hh:02d}:{end_mm:02d}")
    else:
        print("No solution found.")

solve_meeting_scheduling()