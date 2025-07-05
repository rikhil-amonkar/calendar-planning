from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Work hours are 9:00 to 17:00 (9 AM to 5 PM), which is 8 hours or 480 minutes
    total_minutes = 480  # from 9:00 (0) to 17:00 (480)
    meeting_duration = 30
    
    # The start time of the meeting in minutes from 9:00 AM
    start_time = Int('start_time')
    
    # Constraints: start_time must be >= 0 and <= total_minutes - meeting_duration
    s.add(start_time >= 0)
    s.add(start_time <= total_minutes - meeting_duration)
    
    # Define each participant's blocked times in minutes from 9:00 AM
    # Stephanie: 11:00-11:30 (120-150), 14:30-15:00 (330-360)
    stephanie_blocked = [(120, 150), (330, 360)]
    # Joe: 9:00-9:30 (0-30), 10:00-12:00 (60-180), 12:30-13:00 (210-240), 14:00-17:00 (300-480)
    joe_blocked = [(0, 30), (60, 180), (210, 240), (300, 480)]
    # Diana: 9:00-10:30 (0-90), 11:30-12:00 (150-180), 13:00-14:00 (240-300), 14:30-15:30 (330-390), 16:00-17:00 (420-480)
    diana_blocked = [(0, 90), (150, 180), (240, 300), (330, 390), (420, 480)]
    # Deborah: 9:00-10:00 (0-60), 10:30-12:00 (90-180), 12:30-13:00 (210-240), 13:30-14:00 (270-300), 14:30-15:30 (330-390), 16:00-16:30 (420-450)
    deborah_blocked = [(0, 60), (90, 180), (210, 240), (270, 300), (330, 390), (420, 450)]
    
    # For each participant, add constraints that the meeting does not overlap with their blocked times
    # Tyler and Kelly and Hannah have no meetings, so no constraints
    
    # Stephanie's constraints
    for (block_start, block_end) in stephanie_blocked:
        s.add(Or(start_time >= block_end, start_time + meeting_duration <= block_start))
    
    # Joe's constraints
    for (block_start, block_end) in joe_blocked:
        s.add(Or(start_time >= block_end, start_time + meeting_duration <= block_start))
    
    # Diana's constraints
    for (block_start, block_end) in diana_blocked:
        s.add(Or(start_time >= block_end, start_time + meeting_duration <= block_start))
    
    # Deborah's constraints
    for (block_start, block_end) in deborah_blocked:
        s.add(Or(start_time >= block_end, start_time + meeting_duration <= block_start))
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start_min = m[start_time].as_long()
        
        # Convert start_min back to HH:MM format
        start_hh = 9 + start_min // 60
        start_mm = start_min % 60
        end_min = start_min + meeting_duration
        end_hh = 9 + end_min // 60
        end_mm = end_min % 60
        
        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
        print(f"End Time: {end_hh:02d}:{end_mm:02d}")
    else:
        print("No solution found")

solve_scheduling()