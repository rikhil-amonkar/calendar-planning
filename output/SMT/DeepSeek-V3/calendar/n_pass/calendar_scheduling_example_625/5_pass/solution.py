from z3 import *

def solve_scheduling():
    # Create the solver
    s = Solver()

    # Define the possible days (Monday or Tuesday)
    is_monday = Bool('is_monday')

    # Define start and end times (in minutes since 9:00)
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Meeting duration is 30 minutes
    s.add(end_time == start_time + 30)

    # Work hours are 9:00 to 17:00 (480 minutes)
    s.add(start_time >= 0)
    s.add(end_time <= 480)

    # Harold's blocked times:
    # Monday: 9:00-10:00 (0-60), 10:30-17:00 (90-480)
    # Tuesday: 9:00-9:30 (0-30), 10:30-11:30 (90-150),
    #          12:30-13:30 (210-270), 14:30-15:30 (330-390), 16:00-17:00 (420-480)

    # Monday constraints - only available slot is 10:00-10:30
    monday_constraints = And(start_time == 60, end_time == 90)  # Exactly 10:00-10:30
    s.add(Implies(is_monday, monday_constraints))

    # Tuesday constraints - available slots
    tuesday_slots = [
        (30, 60),   # 9:30-10:00
        (150, 210), # 11:30-12:30
        (270, 330), # 13:30-14:30
        (390, 420)  # 15:30-16:00
    ]
    # Create OR of all valid Tuesday slots
    tuesday_constraints = Or([And(start_time == slot[0], end_time == slot[1]) for slot in tuesday_slots])
    s.add(Implies(Not(is_monday), tuesday_constraints))

    # Try to find solution on Tuesday before 14:30 first
    temp_s = Solver()
    temp_s.add(s.assertions())
    temp_s.add(Not(is_monday))
    temp_s.add(end_time <= 270)  # Before 14:30
    if temp_s.check() == sat:
        m = temp_s.model()
    else:
        # Try Tuesday after 14:30
        temp_s = Solver()
        temp_s.add(s.assertions())
        temp_s.add(Not(is_monday))
        temp_s.add(start_time >= 270)
        if temp_s.check() == sat:
            m = temp_s.model()
        else:
            # Try Monday
            temp_s = Solver()
            temp_s.add(s.assertions())
            temp_s.add(is_monday)
            assert temp_s.check() == sat
            m = temp_s.model()

    # Get the solution
    day = "Monday" if is_true(m.eval(is_monday)) else "Tuesday"
    start_min = m.eval(start_time).as_long()
    end_min = m.eval(end_time).as_long()

    # Convert to HH:MM format
    start_hh = 9 + start_min // 60
    start_mm = start_min % 60
    end_hh = 9 + end_min // 60
    end_mm = end_min % 60

    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
    print(f"End Time: {end_hh:02d}:{end_mm:02d}")

solve_scheduling()