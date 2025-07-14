from z3 import *

def solve_scheduling():
    # Create the solver
    s = Solver()

    # Define the possible days (Monday=0, Tuesday=1, Wednesday=2)
    day = Int('day')
    s.add(day >= 0, day <= 2)

    # Define start and end times in minutes from 9:00 (540 minutes)
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Work hours are 9:00 to 17:00 (540 to 1020 minutes)
    s.add(start_time >= 540, end_time <= 1020)
    s.add(end_time == start_time + 60)  # Meeting duration is 1 hour

    # Roy's busy slots for each day in minutes from 9:00
    # Format: (day, start, end)
    roy_busy = [
        # Monday
        (0, 600, 690),   # 10:00-11:30
        (0, 720, 780),   # 12:00-13:00
        (0, 840, 870),    # 14:00-14:30
        (0, 900, 1020),   # 15:00-17:00
        # Tuesday
        (1, 630, 690),    # 10:30-11:30
        (1, 720, 870),    # 12:00-14:30
        (1, 900, 930),    # 15:00-15:30
        (1, 960, 1020),   # 16:00-17:00
        # Wednesday
        (2, 570, 690),    # 9:30-11:30
        (2, 750, 840),    # 12:30-14:00
        (2, 870, 930),    # 14:30-15:30
        (2, 990, 1020)    # 16:30-17:00
    ]

    # Add constraints that the meeting does not overlap with Roy's busy slots
    for busy_day, busy_start, busy_end in roy_busy:
        s.add(Not(And(day == busy_day,
                      start_time < busy_end,
                      end_time > busy_start)))

    # To find the earliest time, we minimize the start_time
    # We'll use a loop to find the earliest feasible solution
    earliest_start = None
    earliest_day = None
    # Check for solutions in order of days and times
    for d in [0, 1, 2]:
        for t in range(540, 1020 - 60 + 1, 15):  # Check every 15 minutes for efficiency
            temp_s = Solver()
            temp_s.add(s.assertions())
            temp_s.add(day == d)
            temp_s.add(start_time == t)
            if temp_s.check() == sat:
                earliest_start = t
                earliest_day = d
                break
        if earliest_start is not None:
            break

    if earliest_start is None:
        print("SOLUTION: No feasible time found.")
    else:
        # Convert day and time to required format
        days = ["Monday", "Tuesday", "Wednesday"]
        start_hh = earliest_start // 60
        start_mm = earliest_start % 60
        end_hh = (earliest_start + 60) // 60
        end_mm = (earliest_start + 60) % 60

        print("SOLUTION:")
        print(f"Day: {days[earliest_day]}")
        print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
        print(f"End Time: {end_hh:02d}:{end_mm:02d}")

solve_scheduling()