from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define variables
    # Time you leave Russian Hill (in minutes since midnight)
    leave_russian_hill = Int('leave_russian_hill')
    # Time you arrive at Pacific Heights
    arrive_pacific_heights = Int('arrive_pacific_heights')
    # Time you start meeting Barbara
    start_meeting = Int('start_meeting')
    # Time you end meeting Barbara
    end_meeting = Int('end_meeting')

    # Constraints
    # You arrive at Russian Hill at 9:00 AM (540 minutes since midnight)
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

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        leave = m[leave_russian_hill].as_long()
        arrive = m[arrive_pacific_heights].as_long()
        start = m[start_meeting].as_long()
        end = m[end_meeting].as_long()
        print(f"Leave Russian Hill at: {leave//60}:{leave%60:02d} AM")
        print(f"Arrive at Pacific Heights at: {arrive//60}:{arrive%60:02d} AM")
        print(f"Meet Barbara from: {start//60}:{start%60:02d} AM to {end//60}:{end%60:02d} {'AM' if end < 720 else 'PM'}")
    else:
        print("No valid schedule found.")

solve_scheduling()