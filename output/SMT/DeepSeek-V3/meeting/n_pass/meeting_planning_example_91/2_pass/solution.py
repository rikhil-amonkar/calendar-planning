from z3 import *

def solve_scheduling_problem():
    # Create solver instance
    s = Solver()

    # Variables (in minutes since 9:00 AM)
    leave_russian_hill = Int('leave_russian_hill')
    arrive_richmond = Int('arrive_richmond')
    meeting_duration = Int('meeting_duration')

    # Constants
    travel_time = 14  # minutes
    min_meeting = 75  # minutes
    daniel_start = 600  # 7:00 PM is 600 minutes after 9:00 AM (10 hours)
    daniel_end = 675    # 8:15 PM is 675 minutes after 9:00 AM (11.25 hours)

    # Constraints
    # 1. Travel time constraint
    s.add(arrive_richmond == leave_russian_hill + travel_time)

    # 2. Must arrive before Daniel leaves
    s.add(arrive_richmond <= daniel_end)

    # 3. Must meet for at least 75 minutes
    s.add(meeting_duration >= min_meeting)
    s.add(arrive_richmond + meeting_duration <= daniel_end)

    # 4. Must arrive during Daniel's availability
    s.add(arrive_richmond >= daniel_start)

    # 5. Can't leave Russian Hill before arrival time (9:00 AM)
    s.add(leave_russian_hill >= 0)

    if s.check() == sat:
        m = s.model()
        lrh = m[leave_russian_hill].as_long()
        ard = m[arrive_richmond].as_long()
        dur = m[meeting_duration].as_long()

        # Convert minutes to time strings
        def to_time(minutes):
            h = 9 + minutes // 60
            m = minutes % 60
            ampm = "AM" if h < 12 else "PM"
            h = h if h <= 12 else h - 12
            return f"{h}:{m:02d} {ampm}"

        print(f"Optimal Schedule:")
        print(f"Leave Russian Hill at: {to_time(lrh)}")
        print(f"Arrive Richmond at: {to_time(ard)}")
        print(f"Meeting duration: {dur} minutes")
    else:
        print("No valid schedule exists")

solve_scheduling_problem()