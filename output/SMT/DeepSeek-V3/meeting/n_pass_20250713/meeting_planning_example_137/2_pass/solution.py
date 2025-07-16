from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Optimize()

    # Define variables
    # Start and end times for meeting Kenneth (in minutes from 9:00 AM)
    k_start = Int('k_start')
    k_end = Int('k_end')
    
    # Start and end times for meeting Barbara (in minutes from 9:00 AM)
    b_start = Int('b_start')
    b_end = Int('b_end')

    # Travel times (in minutes)
    fd_to_china = 5
    fd_to_park = 23
    china_to_park = 23
    park_to_china = 23
    park_to_fd = 26
    china_to_fd = 5

    # Convert friend availability to minutes from 9:00 AM
    # Kenneth is available from 12:00 PM to 3:00 PM (180 to 360 minutes from 9:00 AM)
    k_available_start = 180  # 12:00 PM is 3 hours after 9:00 AM
    k_available_end = 360     # 3:00 PM is 6 hours after 9:00 AM

    # Barbara is available from 8:15 AM to 7:00 PM
    # But we start at 9:00 AM, so Barbara's availability starts at 0 (9:00 AM)
    b_available_start = 0      # 9:00 AM is 0 minutes after 9:00 AM
    b_available_end = 600      # 7:00 PM is 10 hours after 9:00 AM

    # Constraints for Kenneth
    s.add(k_start >= k_available_start)
    s.add(k_end <= k_available_end)
    s.add(k_end - k_start >= 90)  # At least 90 minutes with Kenneth

    # Constraints for Barbara
    s.add(b_start >= b_available_start)
    s.add(b_end <= b_available_end)
    s.add(b_end - b_start >= 45)  # At least 45 minutes with Barbara

    # Constraints for travel and meeting order
    # We start at Financial District at time 0 (9:00 AM)
    # There are two possible orders:
    # 1. Meet Barbara first, then Kenneth
    # 2. Meet Kenneth first, then Barbara

    # Scenario 1: Meet Barbara first, then Kenneth
    scenario1 = And(
        b_start >= 0 + fd_to_park,  # Travel from FD to Park takes 23 minutes
        k_start >= b_end + park_to_china,  # Travel from Park to Chinatown takes 23 minutes
        k_end <= k_available_end  # Ensure Kenneth's meeting ends by 3:00 PM
    )

    # Scenario 2: Meet Kenneth first, then Barbara
    scenario2 = And(
        k_start >= 0 + fd_to_china,  # Travel from FD to Chinatown takes 5 minutes
        b_start >= k_end + china_to_park,  # Travel from Chinatown to Park takes 23 minutes
        b_end <= b_available_end  # Ensure Barbara's meeting ends by 7:00 PM
    )

    # At least one scenario must hold
    s.add(Or(scenario1, scenario2))

    # Maximize the total time spent with friends
    total_time = (k_end - k_start) + (b_end - b_start)
    s.maximize(total_time)

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        # Convert minutes to HH:MM format
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{9 + hours}:{mins:02d} {'AM' if hours < 3 else 'PM'}"
        
        k_start_time = minutes_to_time(m[k_start].as_long())
        k_end_time = minutes_to_time(m[k_end].as_long())
        b_start_time = minutes_to_time(m[b_start].as_long())
        b_end_time = minutes_to_time(m[b_end].as_long())
        
        print(f"Meet Kenneth from {k_start_time} to {k_end_time}")
        print(f"Meet Barbara from {b_start_time} to {b_end_time}")
        print(f"Total time with friends: {m.evaluate(total_time).as_long()} minutes")
    else:
        print("No solution found")

solve_scheduling()