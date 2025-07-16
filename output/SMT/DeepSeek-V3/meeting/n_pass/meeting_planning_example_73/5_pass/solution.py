from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define all variables (in minutes since midnight)
    leave_russian_hill = Int('leave_russian_hill')
    arrive_pacific_heights = Int('arrive_pacific_heights')
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Add constraints
    # Constraint 1: You arrive at Russian Hill at 9:00 AM (540 minutes)
    s.add(leave_russian_hill == 540)
    
    # Constraint 2: Travel time is exactly 7 minutes
    s.add(arrive_pacific_heights == leave_russian_hill + 7)
    
    # Constraint 3: Meeting starts when you arrive
    s.add(meeting_start == arrive_pacific_heights)
    
    # Constraint 4: Meeting lasts exactly 60 minutes
    s.add(meeting_end == meeting_start + 60)
    
    # Constraint 5: Barbara's availability (7:15 AM to 10:00 PM)
    s.add(meeting_start >= 435)  # 7:15 AM = 435 minutes
    s.add(meeting_end <= 1320)   # 10:00 PM = 1320 minutes

    # Check for a valid solution
    if s.check() == sat:
        m = s.model()
        
        # Extract values
        leave = m[leave_russian_hill].as_long()
        arrive = m[arrive_pacific_heights].as_long()
        start = m[meeting_start].as_long()
        end = m[meeting_end].as_long()

        # Helper function to format time
        def format_time(mins):
            h, m = divmod(mins, 60)
            period = 'AM' if h < 12 else 'PM'
            h = h if h <= 12 else h - 12
            return f"{h}:{m:02d} {period}"

        # Print the schedule
        print("Optimal Meeting Schedule:")
        print(f"- Depart Russian Hill at: {format_time(leave)}")
        print(f"- Arrive Pacific Heights at: {format_time(arrive)}")
        print(f"- Meet with Barbara from: {format_time(start)} to {format_time(end)}")
    else:
        print("Error: No valid schedule found")

solve_scheduling()