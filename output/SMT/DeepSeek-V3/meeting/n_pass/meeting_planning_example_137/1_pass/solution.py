from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables
    # Time variables are in minutes since 9:00 AM (540 minutes since midnight)
    start_kenneth = Int('start_kenneth')  # Start time of meeting with Kenneth
    end_kenneth = Int('end_kenneth')      # End time of meeting with Kenneth
    start_barbara = Int('start_barbara')  # Start time of meeting with Barbara
    end_barbara = Int('end_barbara')      # End time of meeting with Barbara

    # Travel times (in minutes)
    fd_to_china = 5
    fd_to_ggp = 23
    china_to_ggp = 23
    ggp_to_china = 23
    china_to_fd = 5
    ggp_to_fd = 26

    # Convert friend availability to minutes since 9:00 AM
    # Kenneth is available from 12:00 PM to 3:00 PM (180 to 360 minutes since 9:00 AM)
    kenneth_start_avail = 180  # 12:00 PM is 3 hours after 9:00 AM
    kenneth_end_avail = 360    # 3:00 PM is 6 hours after 9:00 AM

    # Barbara is available from 8:15 AM to 7:00 PM (but we start at 9:00 AM)
    # Barbara's availability starts at 8:15 AM, but we start at 9:00 AM (0 minutes)
    barbara_start_avail = 0    # 9:00 AM is 0 minutes after 9:00 AM
    barbara_end_avail = 600    # 7:00 PM is 10 hours after 9:00 AM

    # Meeting duration constraints
    min_kenneth_duration = 90
    min_barbara_duration = 45

    # Constraints for Kenneth
    s.add(start_kenneth >= kenneth_start_avail)
    s.add(end_kenneth <= kenneth_end_avail)
    s.add(end_kenneth - start_kenneth >= min_kenneth_duration)

    # Constraints for Barbara
    s.add(start_barbara >= barbara_start_avail)
    s.add(end_barbara <= barbara_end_avail)
    s.add(end_barbara - start_barbara >= min_barbara_duration)

    # Travel constraints
    # We start at Financial District at time 0 (9:00 AM)
    # We can either:
    # 1. Go to Barbara first, then Kenneth
    # 2. Go to Kenneth first, then Barbara
    # We need to model both possibilities and let the solver choose the feasible one.

    # Option 1: Visit Barbara first, then Kenneth
    option1 = And(
        start_barbara >= fd_to_ggp,  # Travel to Barbara takes 23 minutes
        start_kenneth >= end_barbara + china_to_ggp  # Travel from Barbara to Kenneth takes 23 minutes
    )

    # Option 2: Visit Kenneth first, then Barbara
    option2 = And(
        start_kenneth >= fd_to_china,  # Travel to Kenneth takes 5 minutes
        start_barbara >= end_kenneth + ggp_to_china  # Travel from Kenneth to Barbara takes 23 minutes
    )

    # Add the disjunction of the two options
    s.add(Or(option1, option2))

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        # Convert times back to hours/minutes for readability
        def to_time_str(minutes):
            hours = (minutes + 540) // 60  # 9:00 AM is 540 minutes since midnight
            mins = (minutes + 540) % 60
            return f"{hours}:{mins:02d}"

        start_k = m.eval(start_kenneth).as_long()
        end_k = m.eval(end_kenneth).as_long()
        start_b = m.eval(start_barbara).as_long()
        end_b = m.eval(end_barbara).as_long()

        print("SOLUTION:")
        print(f"Meet Kenneth from {to_time_str(start_k)} to {to_time_str(end_k)}")
        print(f"Meet Barbara from {to_time_str(start_b)} to {to_time_str(end_b)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()