from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    # Robert's availability: 11:15 AM to 5:45 PM
    robert_start = (11 * 60 + 15) - (9 * 60)  # 135 minutes after 9:00 AM (11:15 AM is 2h15m after 9:00)
    robert_end = (17 * 60 + 45) - (9 * 60)    # 525 minutes after 9:00 AM (5:45 PM is 8h45m after 9:00)
    
    # Variables for meeting start and end times (relative to 9:00 AM)
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')
    
    # Travel time from Nob Hill to Presidio is 17 minutes
    travel_time = 17
    
    # Constraints
    # 1. Meeting duration is at least 120 minutes
    s.add(meeting_end - meeting_start >= 120)
    
    # 2. Meeting must be within Robert's availability
    s.add(meeting_start >= robert_start)
    s.add(meeting_end <= robert_end)
    
    # 3. Time to travel to Presidio: leave Nob Hill at (meeting_start - travel_time) >= 0 (since we arrive at Nob Hill at 9:00 AM (0 minutes))
    s.add(meeting_start - travel_time >= 0)
    
    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        start = m[meeting_start].as_long()
        end = m[meeting_end].as_long()
        
        # Convert times back to HH:MM format
        def to_time_str(minutes):
            total_minutes = 9 * 60 + minutes
            h = total_minutes // 60
            m = total_minutes % 60
            return f"{h}:{m:02d}"
        
        start_time = to_time_str(start)
        end_time = to_time_str(end)
        
        print(f"SOLUTION: Meet Robert from {start_time} to {end_time}.")
    else:
        print("No feasible schedule found.")

solve_scheduling()