from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Work hours: 9:00 to 17:00 (9:00 is 0, 17:00 is 8*60 = 480 minutes)
    start_work = 9 * 60  # 9:00 in minutes
    end_work = 17 * 60   # 17:00 in minutes
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Possible start time for the meeting (in minutes since 9:00)
    meeting_start = Int('meeting_start')
    
    # Constraint: meeting must start within work hours and end by 17:00
    s.add(meeting_start >= start_work)
    s.add(meeting_start + duration <= end_work)
    
    # Define each participant's busy times in minutes since 9:00
    # Each busy time is a list of (start, end) pairs
    john_busy = [(11*60 + 30, 12*60), (14*60, 14*60 + 30)]
    megan_busy = [(12*60, 12*60 + 30), (14*60, 15*60), (15*60 + 30, 16*60)]
    brandon_busy = []  # No meetings
    kimberly_busy = [(9*60, 9*60 + 30), (10*60, 10*60 + 30), (11*60, 14*60 + 30), (15*60, 16*60), (16*60 + 30, 17*60)]
    sean_busy = [(10*60, 11*60), (11*60 + 30, 14*60), (15*60, 15*60 + 30)]
    lori_busy = [(9*60, 9*60 + 30), (10*60 + 30, 12*60), (13*60, 14*60 + 30), (16*60, 16*60 + 30)]
    
    # Combine all busy times
    all_busy = john_busy + megan_busy + brandon_busy + kimberly_busy + sean_busy + lori_busy
    
    # Add constraints that the meeting does not overlap with any busy time
    for (busy_start, busy_end) in all_busy:
        s.add(Or(
            meeting_start + duration <= busy_start,
            meeting_start >= busy_end
        ))
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start_min = m[meeting_start].as_long()
        
        # Convert minutes back to HH:MM format
        start_hh = start_min // 60
        start_mm = start_min % 60
        end_min = start_min + duration
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