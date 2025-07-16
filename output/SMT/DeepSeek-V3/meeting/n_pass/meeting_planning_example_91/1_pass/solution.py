from z3 import *

def solve_scheduling_problem():
    # Create a solver instance
    s = Solver()

    # Variables
    leave_russian_hill = Int('leave_russian_hill')  # Time in minutes since 9:00 AM
    arrive_richmond = Int('arrive_richmond')        # Time in minutes since 9:00 AM
    leave_richmond = Int('leave_richmond')          # Time in minutes since 9:00 AM

    # Constraints
    # 1. Travel time from Russian Hill to Richmond District is 14 minutes
    s.add(arrive_richmond == leave_russian_hill + 14)

    # 2. Daniel is available from 7:00 PM to 8:15 PM (which is 600 to 675 minutes since 9:00 AM)
    #    We must arrive by 7:00 PM (600 minutes)
    s.add(arrive_richmond <= 600)
    #    We must stay for at least 75 minutes (until 8:15 PM)
    s.add(leave_richmond >= arrive_richmond + 75)
    s.add(leave_richmond <= 675)  # Daniel leaves at 8:15 PM

    # 3. We cannot leave Russian Hill before 9:00 AM (0 minutes)
    s.add(leave_russian_hill >= 0)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        leave_rh = m.evaluate(leave_russian_hill).as_long()
        arrive_rd = m.evaluate(arrive_richmond).as_long()
        leave_rd = m.evaluate(leave_richmond).as_long()

        # Convert minutes to time format
        def minutes_to_time(minutes):
            hours = 9 + (minutes // 60)
            mins = minutes % 60
            return f"{hours}:{mins:02d}"

        print(f"Leave Russian Hill at: {minutes_to_time(leave_rh)}")
        print(f"Arrive at Richmond District at: {minutes_to_time(arrive_rd)}")
        print(f"Leave Richmond District at: {minutes_to_time(leave_rd)}")
    else:
        print("No valid schedule found.")

solve_scheduling_problem()