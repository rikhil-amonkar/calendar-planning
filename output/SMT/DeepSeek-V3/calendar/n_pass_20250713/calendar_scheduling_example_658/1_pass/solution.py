from z3 import *

def solve_scheduling_problem():
    # Create the solver
    s = Solver()

    # Define variables
    day = Int('day')  # 0 for Monday, 1 for Tuesday
    start_time = Int('start_time')  # in minutes from 9:00 (e.g., 9:00 is 0, 10:30 is 90)
    end_time = Int('end_time')

    # Meeting duration is 30 minutes
    s.add(end_time == start_time + 30)

    # Work hours are 9:00-17:00 (0 to 480 minutes)
    s.add(start_time >= 0)
    s.add(end_time <= 480)

    # Day is either 0 (Monday) or 1 (Tuesday)
    s.add(Or(day == 0, day == 1))

    # Shirley's blocked times:
    # Monday: 10:30-11:00 (90-120), 12:00-12:30 (180-210), 16:00-16:30 (420-450)
    # Tuesday: 9:30-10:00 (30-60)
    # Albert's blocked times:
    # Monday: 9:00-17:00 (0-480) -> entire day blocked
    # Tuesday: 9:30-11:00 (30-120), 11:30-12:30 (150-180), 13:00-16:00 (240-420), 16:30-17:00 (450-480)

    # Constraints for Shirley and Albert's schedules
    # If day is Monday (0):
    # Albert is busy all day, so no solution possible on Monday
    s.add(Implies(day == 0, start_time >= 480))  # Makes Monday impossible since start_time must be <= 450 (for end_time 480)

    # If day is Tuesday (1):
    # Shirley's blocked: 30-60
    # Albert's blocked: 30-120, 150-180, 240-420, 450-480
    # Possible slots:
    # Before 9:30 (start_time <= 30 - 30 = 0, but start_time >=0, so 0-30)
    # Between 11:00-11:30 (120-150)
    # Between 12:30-13:00 (180-210)
    # Between 16:00-16:30 (420-450)
    # But Shirley prefers not after 10:30 on Tuesday, so only possible slot is 9:00-9:30 (0-30)
    s.add(Implies(day == 1, And(
        Or(
            And(start_time >= 0, end_time <= 30),  # 9:00-9:30
            # Other possible slots would go here, but Shirley's preference excludes them
            False  # No other slots allowed per preference
        )
    )))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_val = m[start_time].as_long()
        end_val = m[end_time].as_long()

        # Determine day string
        day_str = "Monday" if day_val == 0 else "Tuesday"

        # Calculate start and end times in HH:MM format
        start_hour = 9 + start_val // 60
        start_min = start_val % 60
        end_hour = 9 + end_val // 60
        end_min = end_val % 60

        start_time_str = f"{start_hour:02d}:{start_min:02d}"
        end_time_str = f"{end_hour:02d}:{end_min:02d}"

        # Print the solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling_problem()