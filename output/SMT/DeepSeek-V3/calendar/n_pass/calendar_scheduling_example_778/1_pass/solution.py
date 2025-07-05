from z3 import *

def solve_meeting_schedule():
    # Create the solver
    s = Solver()

    # Define the possible days (Monday=0, Tuesday=1, Wednesday=2)
    day = Int('day')
    s.add(day >= 0, day <= 2)

    # Define the start time in minutes from 9:00 (540 minutes)
    start_time = Int('start_time')
    s.add(start_time >= 540, start_time <= 1020 - 30)  # 17:00 is 1020 minutes, meeting is 30 mins

    # Calculate end time
    end_time = start_time + 30

    # Susan's blocked times in minutes from 9:00
    susan_blocked = [
        (750, 780),   # Monday 12:30-13:00
        (810, 840),    # Monday 13:30-14:00
        (810, 840),    # Tuesday 11:30-12:00
        (570, 630),    # Wednesday 9:30-10:30
        (900, 930),    # Wednesday 14:00-14:30
        (990, 1020),   # Wednesday 15:30-16:30
    ]

    # Sandra's blocked times in minutes from 9:00
    sandra_blocked = [
        (540, 780),    # Monday 9:00-13:00
        (840, 900),     # Monday 14:00-15:00
        (1020, 1050),   # Monday 16:00-16:30 (but Sandra can't meet after 16:00 on Monday)
        (540, 570),     # Tuesday 9:00-9:30
        (690, 780),     # Tuesday 10:30-12:00
        (810, 870),     # Tuesday 12:30-13:30
        (840, 870),     # Tuesday 14:00-14:30
        (960, 1020),    # Tuesday 16:00-17:00
        (540, 750),     # Wednesday 9:00-11:30
        (780, 810),     # Wednesday 12:00-12:30
        (840, 1020),    # Wednesday 13:00-17:00
    ]

    # Susan prefers not to meet on Tuesday (day=1)
    s.add(day != 1)

    # Sandra cannot meet on Monday after 16:00 (day=0 and end_time <= 1020)
    s.add(Not(And(day == 0, end_time > 1020)))

    # Constraints for Susan's availability
    susan_constraints = []
    for (block_start, block_end) in susan_blocked:
        # The meeting should not overlap with any of Susan's blocked times on the chosen day
        susan_constraints.append(Not(And(day == 0, Or(block_start == 750, block_start == 810))))  # Monday
        susan_constraints.append(Not(And(day == 1, block_start == 810)))  # Tuesday
        susan_constraints.append(Not(And(day == 2, Or(block_start == 570, block_start == 900, block_start == 990))))  # Wednesday
    s.add(Or([Not(And(day == d, start_time < block_end, end_time > block_start)) for d in range(3) for (block_start, block_end) in susan_blocked if (d == 0 and (block_start == 750 or block_start == 810)) or (d == 1 and block_start == 810) or (d == 2 and (block_start == 570 or block_start == 900 or block_start == 990))]))

    # Constraints for Sandra's availability
    sandra_constraints = []
    for (block_start, block_end) in sandra_blocked:
        # The meeting should not overlap with any of Sandra's blocked times on the chosen day
        sandra_constraints.append(Not(And(day == 0, Or(block_start == 540, block_start == 840, block_start == 1020))))  # Monday
        sandra_constraints.append(Not(And(day == 1, Or(block_start == 540, block_start == 690, block_start == 810, block_start == 840, block_start == 960))))  # Tuesday
        sandra_constraints.append(Not(And(day == 2, Or(block_start == 540, block_start == 780, block_start == 840))))  # Wednesday
    s.add(Or([Not(And(day == d, start_time < block_end, end_time > block_start)) for d in range(3) for (block_start, block_end) in sandra_blocked if (d == 0 and (block_start == 540 or block_start == 840 or block_start == 1020)) or (d == 1 and (block_start == 540 or block_start == 690 or block_start == 810 or block_start == 840 or block_start == 960)) or (d == 2 and (block_start == 540 or block_start == 780 or block_start == 840))]))

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_val = m[start_time].as_long()
        end_val = start_val + 30

        # Convert day and time to readable format
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[day_val]
        start_hour = start_val // 60
        start_min = start_val % 60
        end_hour = end_val // 60
        end_min = end_val % 60

        # Format the output
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_hour:02d}:{start_min:02d}")
        print(f"End Time: {end_hour:02d}:{end_min:02d}")
    else:
        print("No solution found")

solve_meeting_schedule()