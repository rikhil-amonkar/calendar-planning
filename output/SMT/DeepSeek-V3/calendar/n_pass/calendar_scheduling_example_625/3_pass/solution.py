from z3 import *

def solve_scheduling():
    # Create the solver
    s = Solver()

    # Define the possible days (Monday or Tuesday)
    is_monday = Bool('is_monday')

    # Define start and end times (in minutes since 9:00 to handle arithmetic easily)
    start_time = Int('start_time')  # minutes from 9:00 (e.g., 0 is 9:00, 30 is 9:30)
    end_time = Int('end_time')

    # Meeting duration is 30 minutes
    s.add(end_time == start_time + 30)

    # Work hours are 9:00 to 17:00 (480 minutes from 9:00)
    s.add(start_time >= 0)
    s.add(end_time <= 480)  # 17:00 is 8 hours after 9:00 (480 minutes)

    # Harold's blocked times:
    # Monday: 9:00-10:00 (0-60), 10:30-17:00 (90-480)
    # Tuesday: 9:00-9:30 (0-30), 10:30-11:30 (90-150), 12:30-13:30 (210-270), 14:30-15:30 (330-390), 16:00-17:00 (420-480)

    # Constraints based on the day
    # If Monday, the meeting must not overlap with Harold's blocked times
    monday_constraints = Or(
        And(start_time >= 60, end_time <= 90),  # only possible slot on Monday is 10:00-10:30
    )
    s.add(Implies(is_monday, monday_constraints))

    # If Tuesday, the meeting must not overlap with Harold's blocked times
    tuesday_constraints = Or(
        And(start_time >= 30, end_time <= 90),   # 9:30-10:30 (but Harold is busy 10:30-11:30, so 9:30-10:00 or 10:00-10:30)
        And(start_time >= 150, end_time <= 210), # 11:30-12:30
        And(start_time >= 270, end_time <= 330), # 13:30-14:30
        And(start_time >= 390, end_time <= 420)  # 15:30-16:00
    )
    s.add(Implies(Not(is_monday), tuesday_constraints))

    # Harold prefers to avoid more meetings on Monday, so we prioritize Tuesday
    # We can add a soft constraint to prefer Tuesday before 14:30 (270 minutes from 9:00)
    # To model preferences, we'll first try to find a solution on Tuesday before 14:30
    temp_s = Solver()
    temp_s.add(s.assertions())
    temp_s.add(Not(is_monday))
    temp_s.add(start_time <= 270)  # Before 14:30
    if temp_s.check() == sat:
        m = temp_s.model()
    else:
        # If Tuesday before 14:30 is not possible, try Tuesday after 14:30
        temp_s = Solver()
        temp_s.add(s.assertions())
        temp_s.add(Not(is_monday))
        if temp_s.check() == sat:
            m = temp_s.model()
        else:
            # If Tuesday is not possible, try Monday
            temp_s = Solver()
            temp_s.add(s.assertions())
            temp_s.add(is_monday)
            assert temp_s.check() == sat  # since the problem states a solution exists
            m = temp_s.model()

    # Determine the day
    day_is_monday = is_true(m.eval(is_monday))
    day = "Monday" if day_is_monday else "Tuesday"

    # Get start and end times
    start_min = m.eval(start_time).as_long()
    end_min = m.eval(end_time).as_long()

    # Convert minutes back to HH:MM format
    start_hh = 9 + start_min // 60
    start_mm = start_min % 60
    end_hh = 9 + end_min // 60
    end_mm = end_min % 60

    # Format as 24-hour time with leading zeros
    start_time_str = f"{start_hh:02d}:{start_mm:02d}"
    end_time_str = f"{end_hh:02d}:{end_mm:02d}"

    # Output the solution
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {start_time_str}")
    print(f"End Time: {end_time_str}")

solve_scheduling()