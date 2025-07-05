from z3 import *

def solve_scheduling():
    # Create the solver
    s = Solver()

    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday
    start_time = Int('start_time')  # in minutes from 9:00 (540 minutes in 24-hour format)
    end_time = Int('end_time')

    # Day constraints: day must be 0, 1, or 2
    s.add(Or(day == 0, day == 1, day == 2))

    # Meeting duration is 30 minutes
    s.add(end_time == start_time + 30)

    # Work hours are 9:00 to 17:00 (540 to 1020 minutes in 24-hour format)
    s.add(start_time >= 0)  # 9:00 is 0 minutes from 9:00
    s.add(end_time <= 480)  # 17:00 is 480 minutes from 9:00 (since 17:00 - 9:00 = 8 hours = 480 minutes)

    # Tyler's busy times:
    # Tuesday: 9:00-9:30 (0-30), 14:30-15:00 (330-360)
    # Wednesday: 10:30-11:00 (90-120), 12:30-13:00 (210-240), 13:30-14:00 (270-300), 16:30-17:00 (450-480)
    # Ruth's busy times:
    # Monday: 9:00-10:00 (0-60), 10:30-12:00 (90-180), 12:30-14:30 (210-330), 15:00-16:00 (360-420), 16:30-17:00 (450-480)
    # Tuesday: 9:00-17:00 (0-480)
    # Wednesday: 9:00-17:00 (0-480)

    # Constraints for Tyler's busy times
    # If day is Tuesday (1), the meeting should not overlap with 0-30 or 330-360
    s.add(Implies(day == 1, Not(Or(
        And(start_time < 30, end_time > 0),
        And(start_time < 360, end_time > 330)
    )))
    # If day is Wednesday (2), the meeting should not overlap with 90-120, 210-240, 270-300, 450-480
    s.add(Implies(day == 2, Not(Or(
        And(start_time < 120, end_time > 90),
        And(start_time < 240, end_time > 210),
        And(start_time < 300, end_time > 270),
        And(start_time < 480, end_time > 450)
    )))

    # Constraints for Ruth's busy times
    # If day is Monday (0), the meeting should not overlap with 0-60, 90-180, 210-330, 360-420, 450-480
    s.add(Implies(day == 0, Not(Or(
        And(start_time < 60, end_time > 0),
        And(start_time < 180, end_time > 90),
        And(start_time < 330, end_time > 210),
        And(start_time < 420, end_time > 360),
        And(start_time < 480, end_time > 450)
    )))
    # If day is Tuesday (1), Ruth is busy all day (0-480)
    s.add(Implies(day == 1, Not(And(start_time >= 0, end_time <= 480))))
    # If day is Wednesday (2), Ruth is busy all day (0-480)
    s.add(Implies(day == 2, Not(And(start_time >= 0, end_time <= 480))))

    # Tyler's preference: avoid meetings on Monday before 16:00 (which is 420 minutes from 9:00, since 16:00 is 7 hours after 9:00 = 420 minutes)
    # So if day is Monday, start_time must be >= 420 (but 420 is 16:00, and meeting is 30 minutes, so start_time must be >= 420 - but end_time is start_time +30. So start_time must be >= 420 - but 420 is 16:00, meeting until 16:30. But 16:30 is 450 minutes. But work hours end at 480 (17:00). So start_time must be >= 420 (16:00), but end_time <=480. So start_time <= 450 (since 450 +30=480).
    s.add(Implies(day == 0, start_time >= 420 - 0))  # 420 minutes is 16:00

    # Check for a solution
    if s.check() == sat:
        model = s.model()
        day_val = model[day].as_long()
        start_val = model[start_time].as_long()
        end_val = model[end_time].as_long()

        # Convert day_val to day string
        days = ["Monday", "Tuesday", "Wednesday"]
        selected_day = days[day_val]

        # Convert start and end times to HH:MM format
        start_hour = 9 + (start_val // 60)
        start_min = start_val % 60
        end_hour = 9 + (end_val // 60)
        end_min = end_val % 60

        start_time_str = f"{start_hour:02d}:{start_min:02d}"
        end_time_str = f"{end_hour:02d}:{end_min:02d}"

        # Print the solution
        print("SOLUTION:")
        print(f"Day: {selected_day}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()