from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()
    
    # Convert all times to minutes since 9:00AM for easier calculations
    # Arrival at Russian Hill at 9:00AM is time 0
    # Daniel's window: 7:00PM to 8:15PM is 600 to 675 minutes (since 9:00AM to 7:00PM is 10 hours = 600 minutes)
    daniel_window_start = 600  # 7:00PM in minutes since 9:00AM
    daniel_window_end = 675    # 8:15PM in minutes since 9:00AM
    
    # Meeting start and end times (in minutes since 9:00AM)
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')
    
    # Travel time from Russian Hill to Richmond District is 14 minutes
    travel_time = 14
    
    # Time to leave Russian Hill (must be >= 0, since we arrive at 9:00AM)
    leave_time = Int('leave_time')
    
    # Constraints
    # 1. Meeting must start and end within Daniel's window
    s.add(meeting_start >= daniel_window_start)
    s.add(meeting_end <= daniel_window_end)
    
    # 2. Meeting duration must be at least 75 minutes
    s.add(meeting_end - meeting_start >= 75)
    
    # 3. Leave Russian Hill early enough to arrive by meeting_start
    s.add(leave_time + travel_time <= meeting_start)
    
    # 4. Leave time must be >= 0 (since we arrive at Russian Hill at 9:00AM)
    s.add(leave_time >= 0)
    
    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        # Get the values
        leave = m[leave_time].as_long()
        start = m[meeting_start].as_long()
        end = m[meeting_end].as_long()
        
        # Convert minutes back to time format
        def minutes_to_time(minutes):
            hours = 9 + minutes // 60
            mins = minutes % 60
            ampm = "AM" if hours < 12 else "PM"
            if hours > 12:
                hours -= 12
            return f"{hours}:{mins:02d}{ampm}"
        
        leave_time_str = minutes_to_time(leave)
        meeting_start_str = minutes_to_time(start)
        meeting_end_str = minutes_to_time(end)
        
        print(f"Leave Russian Hill at: {leave_time_str}")
        print(f"Meeting with Daniel starts at: {meeting_start_str}")
        print(f"Meeting with Daniel ends at: {meeting_end_str}")
    else:
        print("No feasible schedule found.")

solve_scheduling()