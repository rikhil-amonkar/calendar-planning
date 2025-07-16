from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Convert all times to minutes since midnight for easier arithmetic
    # Arrival at Nob Hill at 9:00 AM (540 minutes since midnight)
    arrival_time = 9 * 60  # 9:00 AM in minutes since midnight
    
    # Robert's availability: 11:15 AM to 5:45 PM
    robert_start = 11 * 60 + 15  # 11:15 AM in minutes since midnight
    robert_end = 17 * 60 + 45    # 5:45 PM in minutes since midnight
    
    # Travel time from Nob Hill to Presidio is 17 minutes
    travel_time = 17
    
    # Variables for meeting start and end times (in minutes since midnight)
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')
    
    # Constraints
    # 1. Meeting duration is at least 120 minutes
    s.add(meeting_end - meeting_start >= 120)
    
    # 2. Meeting must be within Robert's availability
    s.add(meeting_start >= robert_start)
    s.add(meeting_end <= robert_end)
    
    # 3. Time to travel to Presidio: leave Nob Hill at (meeting_start - travel_time) >= arrival_time
    s.add(meeting_start - travel_time >= arrival_time)
    
    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        start = m[meeting_start].as_long()
        end = m[meeting_end].as_long()
        
        # Convert times back to HH:MM format
        def to_time_str(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h}:{m:02d}"
        
        start_time = to_time_str(start)
        end_time = to_time_str(end)
        
        print(f"SOLUTION: Meet Robert from {start_time} to {end_time}.")
    else:
        print("No feasible schedule found.")

solve_scheduling()