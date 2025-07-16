from z3 import *

def solve_scheduling():
    # Create solver instance
    s = Solver()

    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday
    start_time = Int('start_time')  # in minutes since midnight
    end_time = Int('end_time')

    # Day constraints: day must be 0, 1, or 2
    s.add(Or(day == 0, day == 1, day == 2))

    # Meeting duration is 30 minutes
    s.add(end_time == start_time + 30)

    # Work hours: 9:00 to 17:00 (540 to 1020 minutes)
    s.add(start_time >= 540)
    s.add(end_time <= 1020)

    # Nicole's busy slots
    # Monday: 9:00-9:30 (540-570), 13:00-13:30 (780-810), 14:30-15:30 (870-930)
    # Tuesday: 9:00-9:30 (540-570), 11:30-13:30 (690-810), 14:30-15:30 (870-930)
    # Wednesday: 10:00-11:00 (600-660), 12:30-15:00 (750-900), 16:00-17:00 (960-1020)
    # For Nicole, the meeting must not overlap with any of these slots
    nicole_busy = [
        (0, 540, 570), (0, 780, 810), (0, 870, 930),
        (1, 540, 570), (1, 690, 810), (1, 870, 930),
        (2, 600, 660), (2, 750, 900), (2, 960, 1020)
    ]
    for (d, busy_start, busy_end) in nicole_busy:
        s.add(Not(And(day == d,
                      Or(And(start_time >= busy_start, start_time < busy_end),
                         And(end_time > busy_start, end_time <= busy_end),
                         And(start_time <= busy_start, end_time >= busy_end)))))

    # Ruth's busy slots
    # Monday: 9:00-17:00 (540-1020)
    # Tuesday: 9:00-17:00 (540-1020)
    # Wednesday: 9:00-10:30 (540-630), 11:00-11:30 (660-690), 12:00-12:30 (720-750), 13:30-15:30 (810-930), 16:00-16:30 (960-990)
    # Also, Ruth doesn't want to meet on Wednesday after 13:30 (810 minutes)
    ruth_busy = [
        (0, 540, 1020),
        (1, 540, 1020),
        (2, 540, 630), (2, 660, 690), (2, 720, 750), (2, 810, 930), (2, 960, 990)
    ]
    for (d, busy_start, busy_end) in ruth_busy:
        s.add(Not(And(day == d,
                      Or(And(start_time >= busy_start, start_time < busy_end),
                         And(end_time > busy_start, end_time <= busy_end),
                         And(start_time <= busy_start, end_time >= busy_end)))))
    # Additional constraint: Ruth doesn't want to meet on Wednesday after 13:30 (810 minutes)
    s.add(Not(And(day == 2, start_time >= 810)))

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_val = m[start_time].as_long()
        end_val = m[end_time].as_long()

        # Convert day to string
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[day_val]

        # Convert start and end times to HH:MM format
        start_hh = start_val // 60
        start_mm = start_val % 60
        end_hh = end_val // 60
        end_mm = end_val % 60

        # Format the output
        solution = f"SOLUTION:\nDay: {day_str}\nStart Time: {start_hh:02d}:{start_mm:02d}\nEnd Time: {end_hh:02d}:{end_mm:02d}"
        print(solution)
    else:
        print("No solution found")

solve_scheduling()