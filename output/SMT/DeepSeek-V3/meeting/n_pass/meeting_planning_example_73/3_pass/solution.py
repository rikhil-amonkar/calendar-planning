from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define variables (in minutes since midnight)
    leave_russian_hill = Int('leave_russian_hill')
    arrive_pacific_heights = Int('arrive_pacific_heights')
    start_meeting = Int('start_meeting')
    end_meeting = Int('end_meeting')

    # Constraints
    # You arrive at Russian Hill at 9:00 AM (540 minutes)
    s.add(leave_russian_hill >= 540)
    # Travel time is 7 minutes
    s.add(arrive_pacific_heights == leave_russian_hill + 7)
    # Meeting starts when you arrive
    s.add(start_meeting == arrive_pacific_heights)
    # Meeting lasts at least 60 minutes
    s.add(end_meeting >= start_meeting + 60)
    # Barbara is available from 7:15 AM (435 minutes) to 10:00 PM (1320 minutes)
    s.add(start_meeting >= 435)
    s.add(end_meeting <= 1320)

    # Check if constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        leave = m[leave_russian_hill].as_long()
        arrive = m[arrive_pacific_heights].as_long()
        start = m[start_meeting].as_long()
        end = m[end_meeting].as_long()

        # Convert minutes to readable time format
        def format_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            period = "AM" if hours < 12 else "PM"
            if hours > 12:
                hours -= 12
            return f"{hours}:{mins:02d} {period}"

        print(f"Leave Russian Hill at: {format_time(leave)}")
        print(f"Arrive at Pacific Heights at: {format_time(arrive)}")
        print(f"Meet Barbara from: {format_time(start)} to {format_time(end)}")
    else:
        print("No valid schedule found.")

solve_scheduling()