from z3 import *

def solve_meeting_scheduling():
    # Create the solver
    s = Solver()

    # Define the possible days: 0 for Monday, 1 for Tuesday, 2 for Wednesday
    day = Int('day')
    s.add(day >= 0, day <= 2)

    # Define the start time in minutes from 9:00 (540 minutes in 24-hour format)
    start_time = Int('start_time')
    # Meeting duration is 1 hour (60 minutes)
    duration = 60
    end_time = start_time + duration

    # Work hours are 9:00 (540) to 17:00 (1020)
    s.add(start_time >= 540, end_time <= 1020)

    # Judith's blocked times per day in minutes from 0:00
    # Monday: 12:00-12:30 → 720-750
    # Wednesday: 11:30-12:00 → 690-720
    # Timothy's blocked times per day:
    # Monday: 9:30-10:00 (570-600), 10:30-11:30 (630-690), 12:30-14:00 (750-840), 15:30-17:00 (930-1020)
    # Tuesday: 9:30-13:00 (570-780), 13:30-14:00 (810-840), 14:30-17:00 (870-1020)
    # Wednesday: 9:00-9:30 (540-570), 10:30-11:00 (630-660), 13:30-14:30 (810-870), 15:00-15:30 (900-930), 16:00-16:30 (960-990)

    # Constraints for Judith's blocked times
    def judith_blocked(day_val, start, end):
        # Monday: 12:00-12:30 (720-750)
        if day_val == 0:
            return Or(
                And(start >= 720, start < 750),
                And(end > 720, end <= 750),
                And(start <= 720, end >= 750)
            )
        # Wednesday: 11:30-12:00 (690-720)
        elif day_val == 2:
            return Or(
                And(start >= 690, start < 720),
                And(end > 690, end <= 720),
                And(start <= 690, end >= 720)
            )
        else:
            return False

    # Constraints for Timothy's blocked times
    def timothy_blocked(day_val, start, end):
        if day_val == 0:  # Monday
            blocked_periods = [
                (570, 600),  # 9:30-10:00
                (630, 690),  # 10:30-11:30
                (750, 840),  # 12:30-14:00
                (930, 1020)  # 15:30-17:00
            ]
        elif day_val == 1:  # Tuesday
            blocked_periods = [
                (570, 780),  # 9:30-13:00
                (810, 840),  # 13:30-14:00
                (870, 1020)  # 14:30-17:00
            ]
        elif day_val == 2:  # Wednesday
            blocked_periods = [
                (540, 570),  # 9:00-9:30
                (630, 660),  # 10:30-11:00
                (810, 870),  # 13:30-14:30
                (900, 930),  # 15:00-15:30
                (960, 990)   # 16:00-16:30
            ]
        else:
            blocked_periods = []

        constraints = []
        for (block_start, block_end) in blocked_periods:
            constraints.append(
                Or(
                    And(start >= block_start, start < block_end),
                    And(end > block_start, end <= block_end),
                    And(start <= block_start, end >= block_end)
                )
            )
        return Or(*constraints) if constraints else False

    # Add constraints that the meeting does not overlap with blocked times for either participant
    # Fixed the parenthesis issue here
    s.add(Not(Or(
        And(day == 0, Or(
            judith_blocked(0, start_time, end_time),
            timothy_blocked(0, start_time, end_time)
        )),
        And(day == 1, timothy_blocked(1, start_time, end_time)),
        And(day == 2, Or(
            judith_blocked(2, start_time, end_time),
            timothy_blocked(2, start_time, end_time)
        ))
    )))

    # Judith's preferences: avoid more meetings on Monday (day 0) and before 12:00 (720) on Wednesday (day 2)
    # So, prioritize other days/times. We can add soft constraints or find all solutions and pick the preferred one.
    # Here, we'll first try to find solutions not on Monday or before 12 on Wednesday, then fall back to others if needed.

    # Create a temporary solver to find preferred solutions first
    temp_s = Solver()
    temp_s.add(s.assertions())
    # Add preference: day is not Monday (0)
    temp_s.add(day != 0)
    # Also, if day is Wednesday (2), start_time should be >= 720 (12:00)
    temp_s.add(Implies(day == 2, start_time >= 720))

    solution = None
    if temp_s.check() == sat:
        m = temp_s.model()
        solution = m
    else:
        # No preferred solution, try without preferences
        if s.check() == sat:
            solution = s.model()
        else:
            print("No solution found")
            return

    # Extract solution
    day_val = solution[day].as_long()
    start_val = solution[start_time].as_long()
    end_val = start_val + duration

    # Convert day number to day name
    days = ["Monday", "Tuesday", "Wednesday"]
    day_name = days[day_val]

    # Convert start and end times from minutes to HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    start_time_str = minutes_to_time(start_val)
    end_time_str = minutes_to_time(end_val)

    # Output the solution
    print("SOLUTION:")
    print(f"Day: {day_name}")
    print(f"Start Time: {start_time_str}")
    print(f"End Time: {end_time_str}")

solve_meeting_scheduling()