from z3 import *

def solve_scheduling_problem():
    # Create solver instance
    s = Solver()

    # Variables (in minutes since 9:00 AM)
    leave_russian_hill = Int('leave_russian_hill')
    arrive_richmond = Int('arrive_richmond')

    # Constants
    travel_time = 14  # minutes from Russian Hill to Richmond
    min_meeting = 75  # minutes required with Daniel
    daniel_start = 600  # 7:00 PM is 600 minutes after 9:00 AM (10 hours)
    daniel_end = 675    # 8:15 PM is 675 minutes after 9:00 AM (11.25 hours)

    # Constraints
    # 1. Travel time constraint
    s.add(arrive_richmond == leave_russian_hill + travel_time)

    # 2. Must arrive before Daniel's window ends minus meeting duration
    s.add(arrive_richmond <= daniel_end - min_meeting)

    # 3. Must arrive during Daniel's availability
    s.add(arrive_richmond >= daniel_start)

    # 4. Can't leave Russian Hill before arrival time (9:00 AM)
    s.add(leave_russian_hill >= 0)

    if s.check() == sat:
        m = s.model()
        lrh = m[leave_russian_hill].as_long()
        ard = m[arrive_richmond].as_long()

        # Convert minutes to time strings
        def to_time(minutes):
            total_hours = 9 + minutes // 60
            h = total_hours if total_hours <= 12 else total_hours - 12
            m = minutes % 60
            ampm = "AM" if total_hours < 12 else "PM"
            return f"{h}:{m:02d} {ampm}"

        print("Optimal Schedule:")
        print(f"Leave Russian Hill at: {to_time(lrh)}")
        print(f"Arrive Richmond District at: {to_time(ard)}")
        print(f"Meeting duration: {min_meeting} minutes (until 8:15 PM)")
    else:
        print("No valid schedule exists")

solve_scheduling_problem()