from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    # Barbara's availability: 1:15 PM (13:15) to 6:15 PM (18:15)
    barbara_start = 13 * 60 + 15  # 1:15 PM in minutes
    barbara_end = 18 * 60 + 15    # 6:15 PM in minutes
    
    # Travel time from Russian Hill to Richmond District: 14 minutes
    travel_time = 14
    
    # Variables for the meeting start and end times (in minutes since midnight)
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')
    
    # Constraints
    # 1. Meeting must start and end within Barbara's availability
    s.add(meeting_start >= barbara_start)
    s.add(meeting_end <= barbara_end)
    
    # 2. Meeting duration must be at least 45 minutes
    s.add(meeting_end - meeting_start >= 45)
    
    # 3. Travel time constraint: must leave Russian Hill early enough to arrive by meeting_start
    # Arrival at Russian Hill is at 9:00 AM (540 minutes)
    # Time available for travel and other activities before meeting: meeting_start - travel_time >= 540
    s.add(meeting_start - travel_time >= 9 * 60)  # 9:00 AM is 540 minutes
    
    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        start = m[meeting_start].as_long()
        end = m[meeting_end].as_long()
        
        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            hh = minutes // 60
            mm = minutes % 60
            return f"{hh}:{mm:02d}"
        
        start_time = minutes_to_time(start)
        end_time = minutes_to_time(end)
        
        print(f"Meeting with Barbara can be scheduled from {start_time} to {end_time}.")
    else:
        print("No valid schedule found.")

solve_scheduling()