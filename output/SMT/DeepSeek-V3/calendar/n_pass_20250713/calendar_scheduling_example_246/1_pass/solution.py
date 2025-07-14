from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Define the work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    
    # Meeting duration is 30 minutes
    meeting_duration = 30
    
    # Define the start time of the meeting as an integer variable
    meeting_start = Int('meeting_start')
    
    # Constraint: meeting must start within work hours and end before work ends
    s.add(meeting_start >= work_start)
    s.add(meeting_start + meeting_duration <= work_end)
    
    # Each participant's busy slots in minutes since midnight
    busy_slots = {
        'Jacob': [(13 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60)],
        'Diana': [(9 * 60 + 30, 10 * 60), (11 * 60 + 30, 12 * 60), (13 * 60, 13 * 60 + 30), (16 * 60, 16 * 60 + 30)],
        'Adam': [(9 * 60 + 30, 10 * 60 + 30), (11 * 60, 12 * 60 + 30), (15 * 60 + 30, 16 * 60)],
        'Angela': [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 12 * 60), (13 * 60, 15 * 60 + 30), (16 * 60, 16 * 60 + 30)],
        'Dennis': [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 11 * 60 + 30), (13 * 60, 15 * 60), (16 * 60 + 30, 17 * 60)],
    }
    
    # Add constraints that the meeting does not overlap with any busy slot
    for person in busy_slots:
        for start, end in busy_slots[person]:
            s.add(Or(
                meeting_start + meeting_duration <= start,
                meeting_start >= end
            ))
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start_min = m[meeting_start].as_long()
        
        # Convert minutes back to HH:MM format
        start_hh = start_min // 60
        start_mm = start_min % 60
        end_min = start_min + meeting_duration
        end_hh = end_min // 60
        end_mm = end_min % 60
        
        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
        print(f"End Time: {end_hh:02d}:{end_mm:02d}")
    else:
        print("No solution found")

solve_scheduling()