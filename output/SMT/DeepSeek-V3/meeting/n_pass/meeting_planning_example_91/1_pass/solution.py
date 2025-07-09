from z3 import *

def solve_scheduling():
    # Create a solver instance
    s = Solver()

    # Variables representing the times in minutes since 9:00 AM
    leave_russian_hill = Int('leave_russian_hill')  # Time to leave Russian Hill
    arrive_richmond = Int('arrive_richmond')        # Time to arrive at Richmond
    leave_richmond = Int('leave_richmond')          # Time to leave Richmond
    arrive_back_russian_hill = Int('arrive_back_russian_hill')  # Time to return to Russian Hill

    # Travel times in minutes
    travel_to_richmond = 14
    travel_back_russian = 13

    # Daniel's availability: 7:00 PM to 8:15 PM is 600 to 675 minutes since 9:00 AM (10 hours = 600 mins, 11.25 hours = 675 mins)
    daniel_start = 600  # 7:00 PM is 10 hours after 9:00 AM
    daniel_end = 675    # 8:15 PM is 11.25 hours after 9:00 AM

    # Constraints
    # 1. You must leave Russian Hill after or at 9:00 AM (time >= 0)
    s.add(leave_russian_hill >= 0)
    # 2. Arrival at Richmond is leave_russian_hill + travel time
    s.add(arrive_richmond == leave_russian_hill + travel_to_richmond)
    # 3. You must arrive at Richmond by 7:00 PM (daniel_start)
    s.add(arrive_richmond <= daniel_start)
    # 4. You must leave Richmond at or after 8:15 PM (daniel_end)
    s.add(leave_richmond >= daniel_end)
    # 5. Time spent with Daniel is at least 75 minutes (daniel_end - arrive_richmond >= 75)
    # But since Daniel's window is exactly 75 minutes, and you must be there for the entire window, this is already enforced by constraints 3 and 4.
    # 6. Return trip: arrive_back_russian_hill = leave_richmond + travel_back_russian
    s.add(arrive_back_russian_hill == leave_richmond + travel_back_russian)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        print("Feasible schedule found:")
        print(f"Leave Russian Hill at: {m[leave_russian_hill].as_long()} minutes after 9:00 AM")
        print(f"Arrive at Richmond at: {m[arrive_richmond].as_long()} minutes after 9:00 AM")
        print(f"Leave Richmond at: {m[leave_richmond].as_long()} minutes after 9:00 AM")
        print(f"Arrive back at Russian Hill at: {m[arrive_back_russian_hill].as_long()} minutes after 9:00 AM")
    else:
        print("No feasible schedule found")

solve_scheduling()