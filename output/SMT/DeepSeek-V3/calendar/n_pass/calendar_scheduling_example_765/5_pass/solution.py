from z3 import *

def solve_meeting_scheduling():
    # Create the solver
    s = Solver()

    # Define possible days (Monday=0, Tuesday=1, Wednesday=2)
    day = Int('day')
    s.add(day >= 0, day <= 2)

    # Define start and end times in minutes from 9:00 (540 minutes)
    start_time = Int('start_time')
    end_time = Int('end_time')
    meeting_duration = 30  # minutes

    # Work hours: 9:00 (540) to 17:00 (1020)
    s.add(start_time >= 540, end_time <= 1020)
    s.add(end_time == start_time + meeting_duration)

    # Joshua's busy times (day, start, end in minutes from 9:00)
    joshua_busy = [
        (0, 900, 930),    # Monday 15:00-15:30
        (1, 690, 720),    # Tuesday 11:30-12:00
        (1, 780, 810),    # Tuesday 13:00-13:30
        (1, 870, 900)     # Tuesday 14:30-15:00
    ]

    # Joyce's busy times (day, start, end in minutes from 9:00)
    joyce_busy = [
        (0, 540, 570),    # Monday 9:00-9:30
        (0, 600, 660),    # Monday 10:00-11:00
        (0, 690, 720),    # Monday 11:30-12:30
        (0, 780, 900),    # Monday 13:00-15:00
        (0, 930, 1020),   # Monday 15:30-17:00
        (1, 540, 1020),   # Tuesday 9:00-17:00 (all day)
        (2, 540, 570),    # Wednesday 9:00-9:30
        (2, 600, 660),    # Wednesday 10:00-11:00
        (2, 750, 930),    # Wednesday 12:30-15:30
        (2, 960, 990)     # Wednesday 16:00-16:30
    ]

    # Joyce prefers not to meet on Monday before 12:00 (720 minutes from midnight, 180 from 9:00)
    s.add(Not(And(day == 0, start_time < 180)))

    # Ensure the meeting doesn't conflict with Joshua's schedule
    for d, busy_start, busy_end in joshua_busy:
        s.add(Not(And(day == d,
                     Or(start_time < busy_end, end_time > busy_start)))

    # Ensure the meeting doesn't conflict with Joyce's schedule
    for d, busy_start, busy_end in joyce_busy:
        s.add(Not(And(day == d,
                     Or(start_time < busy_end, end_time > busy_start)))

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_val = m[start_time].as_long()
        end_val = m[end_time].as_long()

        # Convert day to string
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[day_val]

        # Convert minutes to HH:MM format
        def minutes_to_time(minutes):
            hh = (540 + minutes) // 60
            mm = (540 + minutes) % 60
            return f"{hh:02d}:{mm:02d}"

        start_time_str = minutes_to_time(start_val)
        end_time_str = minutes_to_time(end_val)

        # Print the solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_meeting_scheduling()