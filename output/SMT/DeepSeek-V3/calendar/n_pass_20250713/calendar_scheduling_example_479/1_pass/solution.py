from z3 import *

def solve_meeting_schedule():
    # Create a solver instance
    s = Solver()

    # Define the time range in minutes from 9:00 (540 minutes) to 17:00 (1020 minutes)
    start_work = 9 * 60
    end_work = 17 * 60
    meeting_duration = 60  # 1 hour in minutes

    # The meeting start time variable (in minutes since midnight)
    meeting_start = Int('meeting_start')
    
    # Constraints: meeting must be within work hours and duration fits
    s.add(meeting_start >= start_work)
    s.add(meeting_start + meeting_duration <= end_work)

    # Define each person's busy intervals in minutes
    busy_intervals = {
        'Joshua': [(11*60, 12*60 + 30), (13*60 + 30, 14*60 + 30), (16*60 + 30, 17*60)],
        'Jerry': [(9*60, 9*60 + 30), (10*60 + 30, 12*60), (12*60 + 30, 13*60), 
                  (13*60 + 30, 14*60), (14*60 + 30, 15*60), (15*60 + 30, 16*60)],
        'Jesse': [(9*60, 9*60 + 30), (10*60 + 30, 12*60), (12*60 + 30, 13*60), 
                  (14*60 + 30, 15*60), (15*60 + 30, 16*60 + 30)],
        'Kenneth': [(10*60 + 30, 12*60 + 30), (13*60 + 30, 14*60), (14*60 + 30, 15*60), 
                    (15*60 + 30, 16*60), (16*60 + 30, 17*60)]
    }

    # For each person's busy intervals, add constraints that the meeting does not overlap
    for person, intervals in busy_intervals.items():
        for (busy_start, busy_end) in intervals:
            # The meeting does not overlap with this busy interval
            s.add(Or(
                meeting_start + meeting_duration <= busy_start,
                meeting_start >= busy_end
            ))

    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        start_minutes = m[meeting_start].as_long()
        
        # Convert minutes back to HH:MM format
        start_hh = start_minutes // 60
        start_mm = start_minutes % 60
        end_minutes = start_minutes + meeting_duration
        end_hh = end_minutes // 60
        end_mm = end_minutes % 60
        
        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
        print(f"End Time: {end_hh:02d}:{end_mm:02d}")
    else:
        print("No solution found")

solve_meeting_schedule()