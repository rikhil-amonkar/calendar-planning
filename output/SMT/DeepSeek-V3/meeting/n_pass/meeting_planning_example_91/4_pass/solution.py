from z3 import *

def solve_scheduling_problem():
    # Initialize solver
    s = Solver()

    # Define variables (minutes since 9:00 AM)
    departure = Int('departure')  # When to leave Russian Hill
    arrival = Int('arrival')      # When to arrive in Richmond

    # Constants
    TRAVEL_TIME = 14      # Minutes to Richmond
    MIN_MEETING = 75      # Required meeting duration
    DANIEL_START = 600    # 7:00 PM (600 minutes after 9:00 AM)
    DANIEL_END = 675      # 8:15 PM (675 minutes after 9:00 AM)

    # Constraints
    # 1. Travel time relationship
    s.add(arrival == departure + TRAVEL_TIME)

    # 2. Must arrive early enough to get full meeting time
    s.add(arrival <= DANIEL_END - MIN_MEETING)

    # 3. Must arrive during Daniel's availability
    s.add(arrival >= DANIEL_START)

    # 4. Can't leave before 9:00 AM
    s.add(departure >= 0)

    if s.check() == sat:
        m = s.model()
        depart_time = m[departure].as_long()
        arrive_time = m[arrival].as_long()

        # Helper function to format time
        def format_time(minutes):
            hours = 9 + minutes // 60
            mins = minutes % 60
            period = "AM" if hours < 12 else "PM"
            display_hour = hours if hours <= 12 else hours - 12
            return f"{display_hour}:{mins:02d} {period}"

        print("\nOptimal Meeting Schedule:")
        print(f"• Depart Russian Hill at: {format_time(depart_time)}")
        print(f"• Arrive Richmond District at: {format_time(arrive_time)}")
        print(f"• Meet Daniel from 7:00 PM to 8:15 PM (75 minutes)")
    else:
        print("No valid schedule exists that meets all constraints.")

# Run the solver
solve_scheduling_problem()