from z3 import *

def solve_scheduling():
    # Create the solver
    s = Solver()

    # Define the possible days (Monday=0, Tuesday=1)
    day = Int('day')
    s.add(Or(day == 0, day == 1))

    # Define the start time in minutes from 9:00 (540 minutes)
    start_time = Int('start_time')
    s.add(start_time >= 540)  # 9:00
    s.add(start_time <= 1020) # 17:00 - 30 minutes (since meeting is 30 mins)

    # Meeting duration is 30 minutes
    end_time = start_time + 30
    s.add(end_time <= 1020)  # Ensure end time is within 17:00

    # Amanda's busy times (converted to minutes from 0:00)
    amanda_busy = [
        # Monday
        [(540, 630), (660, 690), (750, 780), (810, 840), (870, 900), (960, 990)],
        # Tuesday
        [(540, 570), (600, 630), (690, 720), (810, 870), (930, 960), (990, 1020)]
    ]

    # Nathan's busy times (converted to minutes from 0:00)
    nathan_busy = [
        # Monday
        [(600, 630), (660, 690), (810, 870), (960, 990)],
        # Tuesday
        [(540, 630), (660, 780), (810, 840), (870, 930), (960, 990)]
    ]

    # Add constraints for Amanda's busy times
    for day_idx in range(2):
        for (busy_start, busy_end) in amanda_busy[day_idx]:
            s.add(Not(And(day == day_idx,
                          start_time < busy_end,
                          end_time > busy_start)))

    # Add constraints for Nathan's busy times
    for day_idx in range(2):
        for (busy_start, busy_end) in nathan_busy[day_idx]:
            s.add(Not(And(day == day_idx,
                          start_time < busy_end,
                          end_time > busy_start)))

    # Amanda does not want to meet on Tuesday after 11:00 (660 minutes)
    s.add(Not(And(day == 1, start_time >= 660)))

    # Nathan cannot meet on Monday
    s.add(day != 0)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_val = m[start_time].as_long()
        end_val = start_val + 30

        # Convert day to string
        day_str = "Monday" if day_val == 0 else "Tuesday"

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