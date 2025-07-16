from z3 import *

def solve_scheduling():
    # Create the solver
    s = Solver()

    # Days: Monday (0), Tuesday (1), Wednesday (2)
    day = Int('day')
    s.add(day >= 0, day <= 2)

    # Start time in minutes from 9:00 (540 minutes) to 17:00 (1020 minutes)
    start_time = Int('start_time')
    s.add(start_time >= 540, start_time <= 990)  # 30 minutes before 17:00

    # Duration is 30 minutes
    end_time = start_time + 30
    s.add(end_time <= 1020)  # 17:00 is 1020 minutes

    # Tyler's constraints
    # Tyler is busy:
    # Tuesday 9:00-9:30 (540-570), 14:30-15:00 (870-900)
    # Wednesday 10:30-11:00 (630-660), 12:30-13:00 (750-780), 13:30-14:00 (810-840), 16:30-17:00 (990-1020)
    # Also, Tyler prefers to avoid Monday before 16:00 (i.e., before 960 minutes)
    # So on Monday (day 0), start_time must be >= 960 or not on Monday

    # Tyler's busy times per day
    # For each day, if day is X, then the meeting should not overlap with the busy times on day X
    # Tuesday (day 1)
    tyler_tuesday1_start = 540
    tyler_tuesday1_end = 570
    tyler_tuesday2_start = 870
    tyler_tuesday2_end = 900

    # Wednesday (day 2)
    tyler_wednesday1_start = 630
    tyler_wednesday1_end = 660
    tyler_wednesday2_start = 750
    tyler_wednesday2_end = 780
    tyler_wednesday3_start = 810
    tyler_wednesday3_end = 840
    tyler_wednesday4_start = 990
    tyler_wednesday4_end = 1020

    # Tyler's constraints: for each day, if the meeting is on that day, it must not overlap with any busy slot
    # For day 1 (Tuesday)
    s.add(Implies(day == 1, Not(Or(
        And(start_time < tyler_tuesday1_end, end_time > tyler_tuesday1_start),
        And(start_time < tyler_tuesday2_end, end_time > tyler_tuesday2_start)
    )))

    # For day 2 (Wednesday)
    s.add(Implies(day == 2, Not(Or(
        And(start_time < tyler_wednesday1_end, end_time > tyler_wednesday1_start),
        And(start_time < tyler_wednesday2_end, end_time > tyler_wednesday2_start),
        And(start_time < tyler_wednesday3_end, end_time > tyler_wednesday3_start),
        And(start_time < tyler_wednesday4_end, end_time > tyler_wednesday4_start)
    ))))

    # Tyler's preference: avoid Monday before 16:00 (960 minutes)
    s.add(Implies(day == 0, start_time >= 960))

    # Ruth's constraints
    # Ruth's busy times:
    # Monday: 9:00-10:00 (540-600), 10:30-12:00 (630-720), 12:30-14:30 (750-870), 15:00-16:00 (900-960), 16:30-17:00 (990-1020)
    # Tuesday: 9:00-17:00 (540-1020) → entire day blocked
    # Wednesday: 9:00-17:00 (540-1020) → entire day blocked

    # So the meeting cannot be on Tuesday (day 1) or Wednesday (day 2) for Ruth
    s.add(day != 1, day != 2)  # So day must be 0 (Monday)

    # On Monday, the meeting must not overlap with any of Ruth's busy times
    ruth_monday1_start = 540
    ruth_monday1_end = 600
    ruth_monday2_start = 630
    ruth_monday2_end = 720
    ruth_monday3_start = 750
    ruth_monday3_end = 870
    ruth_monday4_start = 900
    ruth_monday4_end = 960
    ruth_monday5_start = 990
    ruth_monday5_end = 1020

    s.add(Implies(day == 0, Not(Or(
        And(start_time < ruth_monday1_end, end_time > ruth_monday1_start),
        And(start_time < ruth_monday2_end, end_time > ruth_monday2_start),
        And(start_time < ruth_monday3_end, end_time > ruth_monday3_start),
        And(start_time < ruth_monday4_end, end_time > ruth_monday4_start),
        And(start_time < ruth_monday5_end, end_time > ruth_monday5_start)
    ))))

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_val = m[start_time].as_long()

        # Convert day_val to day name
        days = ["Monday", "Tuesday", "Wednesday"]
        day_name = days[day_val]

        # Convert start_val to HH:MM
        hours = start_val // 60
        minutes = start_val % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"

        # End time is start + 30 minutes
        end_val = start_val + 30
        end_hours = end_val // 60
        end_minutes = end_val % 60
        end_time_str = f"{end_hours:02d}:{end_minutes:02d}"

        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()