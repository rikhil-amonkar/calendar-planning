from z3 import *

def solve_scheduling_problem():
    # Initialize solver
    solver = Solver()

    # Define variables (in minutes since midnight)
    # We'll use minutes since midnight for easier calculations
    leave_russian_hill = Int('leave_russian_hill')  # Departure time from Russian Hill
    arrive_richmond = Int('arrive_richmond')      # Arrival time in Richmond District

    # Constants (all times in minutes since midnight)
    ARRIVAL_AT_RUSSIAN_HILL = 9 * 60  # 9:00 AM
    TRAVEL_TIME = 14                   # Minutes to Richmond
    MIN_MEETING_DURATION = 75          # Required meeting time
    DANIEL_START = 19 * 60             # 7:00 PM
    DANIEL_END = 20 * 60 + 15          # 8:15 PM

    # Constraints
    # 1. Can't leave Russian Hill before arriving there at 9:00 AM
    solver.add(leave_russian_hill >= ARRIVAL_AT_RUSSIAN_HILL)

    # 2. Travel time relationship
    solver.add(arrive_richmond == leave_russian_hill + TRAVEL_TIME)

    # 3. Must arrive early enough to get full meeting duration
    solver.add(arrive_richmond <= DANIEL_END - MIN_MEETING_DURATION)

    # 4. Must arrive during Daniel's availability window
    solver.add(arrive_richmond >= DANIEL_START)

    if solver.check() == sat:
        model = solver.model()
        depart = model[leave_russian_hill].as_long()
        arrive = model[arrive_richmond].as_long()

        # Convert minutes since midnight to readable time
        def format_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            period = "AM" if hours < 12 else "PM"
            display_hour = hours if hours <= 12 else hours - 12
            return f"{display_hour}:{mins:02d} {period}"

        print("\nOptimal Meeting Schedule:")
        print(f"1. Depart Russian Hill at: {format_time(depart)}")
        print(f"2. Arrive Richmond District at: {format_time(arrive)}")
        print(f"3. Meet Daniel from 7:00 PM to 8:15 PM (75 minutes)")
    else:
        print("No valid schedule exists that meets all constraints.")

# Run the solver
solve_scheduling_problem()