from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Define the work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    
    # Meeting duration is 30 minutes
    meeting_duration = 30
    
    # Possible start times are every minute within work hours
    start_time = Int('start_time')
    s.add(start_time >= work_start)
    s.add(start_time <= work_end - meeting_duration)
    
    # Encode each person's busy times (in minutes since midnight)
    # Katherine: 12:00-12:30, 13:00-14:30
    katherine_busy = Or(
        And(start_time < 12 * 60 + 30, start_time + meeting_duration > 12 * 60),
        And(start_time < 14 * 60 + 30, start_time + meeting_duration > 13 * 60)
    )
    s.add(Not(katherine_busy))
    
    # Rebecca: no meetings
    # No constraints needed
    
    # Julie: 9:00-9:30, 10:30-11:00, 13:30-14:00, 15:00-15:30
    julie_busy = Or(
        And(start_time < 9 * 60 + 30, start_time + meeting_duration > 9 * 60),
        And(start_time < 11 * 60, start_time + meeting_duration > 10 * 60 + 30),
        And(start_time < 14 * 60, start_time + meeting_duration > 13 * 60 + 30),
        And(start_time < 15 * 60 + 30, start_time + meeting_duration > 15 * 60)
    )
    s.add(Not(julie_busy))
    
    # Angela: 9:00-10:00, 10:30-11:00, 11:30-14:00, 14:30-15:00, 16:30-17:00
    # Also prefers to avoid before 15:00
    angela_busy = Or(
        And(start_time < 10 * 60, start_time + meeting_duration > 9 * 60),
        And(start_time < 11 * 60, start_time + meeting_duration > 10 * 60 + 30),
        And(start_time < 14 * 60, start_time + meeting_duration > 11 * 60 + 30),
        And(start_time < 15 * 60, start_time + meeting_duration > 14 * 60 + 30),
        And(start_time < 17 * 60, start_time + meeting_duration > 16 * 60 + 30),
        start_time + meeting_duration <= 15 * 60  # Angela's preference: avoid before 15:00
    )
    s.add(Not(angela_busy))
    
    # Nicholas: 9:30-11:00, 11:30-13:30, 14:00-16:00, 16:30-17:00
    nicholas_busy = Or(
        And(start_time < 11 * 60, start_time + meeting_duration > 9 * 60 + 30),
        And(start_time < 13 * 60 + 30, start_time + meeting_duration > 11 * 60 + 30),
        And(start_time < 16 * 60, start_time + meeting_duration > 14 * 60),
        And(start_time < 17 * 60, start_time + meeting_duration > 16 * 60 + 30)
    )
    s.add(Not(nicholas_busy))
    
    # Carl: 9:00-11:00, 11:30-12:30, 13:00-14:30, 15:00-16:00, 16:30-17:00
    carl_busy = Or(
        And(start_time < 11 * 60, start_time + meeting_duration > 9 * 60),
        And(start_time < 12 * 60 + 30, start_time + meeting_duration > 11 * 60 + 30),
        And(start_time < 14 * 60 + 30, start_time + meeting_duration > 13 * 60),
        And(start_time < 16 * 60, start_time + meeting_duration > 15 * 60),
        And(start_time < 17 * 60, start_time + meeting_duration > 16 * 60 + 30)
    )
    s.add(Not(carl_busy))
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start = m[start_time].as_long()
        
        # Convert start time from minutes to HH:MM
        start_hh = start // 60
        start_mm = start % 60
        end = start + meeting_duration
        end_hh = end // 60
        end_mm = end % 60
        
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
        print(f"End Time: {end_hh:02d}:{end_mm:02d}")
    else:
        print("No solution found")

solve_scheduling()