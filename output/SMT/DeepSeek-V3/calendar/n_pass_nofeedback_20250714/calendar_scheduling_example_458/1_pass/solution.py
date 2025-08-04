from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()
    
    # Convert all times to minutes since 9:00 (540 minutes in 24-hour format)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30
    
    # Start time variable in minutes since 9:00
    start_time = Int('start_time')
    
    # Constraints: start_time must be within work hours and allow 30-minute meeting
    s.add(start_time >= work_start)
    s.add(start_time + meeting_duration <= work_end)
    
    # Wayne's preference: meeting starts at or after 14:00
    s.add(start_time >= 14 * 60)
    
    # Define each person's busy intervals in minutes since 9:00
    # Format: list of (start, end) tuples in minutes
    busy_intervals = {
        'Wayne': [],
        'Melissa': [(10*60, 11*60), (12*60 + 30, 14*60), (15*60, 15*60 + 30)],
        'Catherine': [],
        'Gregory': [(12*60 + 30, 13*60), (15*60 + 30, 16*60)],
        'Victoria': [(9*60, 9*60 + 30), (10*60 + 30, 11*60 + 30), (13*60, 14*60), (14*60 + 30, 15*60), (15*60 + 30, 16*60 + 30)],
        'Thomas': [(10*60, 12*60), (12*60 + 30, 13*60), (14*60 + 30, 16*60)],
        'Jennifer': [(9*60, 9*60 + 30), (10*60, 10*60 + 30), (11*60, 13*60), (13*60 + 30, 14*60 + 30), (15*60, 15*60 + 30), (16*60, 16*60 + 30)]
    }
    
    # For each person, add constraints that the meeting does not overlap with their busy times
    for person, intervals in busy_intervals.items():
        for (busy_start, busy_end) in intervals:
            # The meeting should not overlap with this busy interval
            # So either meeting ends before busy_start or starts after busy_end
            s.add(Or(
                start_time + meeting_duration <= busy_start,
                start_time >= busy_end
            ))
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start_min = m[start_time].as_long()
        
        # Convert start_min back to HH:MM
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