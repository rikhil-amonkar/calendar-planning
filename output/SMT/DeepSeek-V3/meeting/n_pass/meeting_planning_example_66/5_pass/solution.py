from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()
    
    # Time constants (in minutes since midnight)
    arrival_nob_hill = 9 * 60      # 9:00 AM
    robert_start = 11 * 60 + 15    # 11:15 AM
    robert_end = 17 * 60 + 45      # 5:45 PM
    travel_time = 17               # Minutes
    
    # Decision variables (in minutes since midnight)
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')
    
    # Constraints
    # 1. Meeting duration at least 120 minutes
    s.add(meeting_end - meeting_start >= 120)
    
    # 2. Within Robert's availability
    s.add(meeting_start >= robert_start)
    s.add(meeting_end <= robert_end)
    
    # 3. Travel time constraint
    s.add(meeting_start - travel_time >= arrival_nob_hill)
    
    # Solve
    if s.check() == sat:
        m = s.model()
        start = m[meeting_start].as_long()
        end = m[meeting_end].as_long()
        
        # Format times as HH:MM AM/PM
        def format_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            period = "AM" if hours < 12 else "PM"
            if hours > 12:
                hours -= 12
            elif hours == 0:
                hours = 12
            return f"{hours}:{mins:02d} {period}"
        
        print(f"SOLUTION: Meet Robert from {format_time(start)} to {format_time(end)}.")
    else:
        print("No feasible schedule found.")

solve_scheduling()