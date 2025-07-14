from z3 import *

def solve_scheduling_problem():
    # Create the solver
    s = Solver()

    # Define variables
    day = Int('day')  # 0 for Monday, 1 for Tuesday
    start_time = Int('start_time')  # in minutes from 9:00 (0 to 480)
    end_time = Int('end_time')

    # Meeting duration is 30 minutes
    s.add(end_time == start_time + 30)

    # Work hours are 9:00 to 17:00 (480 minutes)
    s.add(start_time >= 0)
    s.add(end_time <= 480)

    # Day must be either 0 (Monday) or 1 (Tuesday)
    s.add(Or(day == 0, day == 1))

    # Jesse's busy slots:
    # Monday: 13:30-14:00 (4.5 hours from 9:00 is 270 to 300 minutes), 14:30-15:00 (330 to 360)
    # Tuesday: 9:00-9:30 (0 to 30), 13:00-13:30 (240 to 270), 14:00-15:00 (300 to 360)
    # Lawrence's busy slots:
    # Monday: 9:00-17:00 (0 to 480) --> entire day, so no availability on Monday
    # Tuesday: 9:30-10:30 (30 to 90), 11:30-12:30 (150 to 180), 13:00-13:30 (240 to 270), 14:30-15:00 (330 to 360), 15:30-16:30 (390 to 450)
    # Lawrence cannot meet after 16:30 on Tuesday (so end_time <= 450 minutes on Tuesday)

    # Constraints for Jesse and Lawrence's availability

    # For Monday (day 0):
    # Lawrence is busy all day on Monday (0-480 minutes), so meeting cannot be on Monday
    s.add(Implies(day == 0, False))  # No solution on Monday

    # For Tuesday (day 1):
    # Jesse's busy slots on Tuesday: 0-30, 240-270, 300-360
    # Lawrence's busy slots on Tuesday: 30-90, 150-180, 240-270, 330-360, 390-450
    # Also, end_time <= 450 on Tuesday (since Lawrence can't meet after 16:30)

    # So on Tuesday, the meeting must not overlap with any of these slots for both participants
    s.add(Implies(day == 1, start_time >= 0))  # Redundant, but for clarity
    s.add(Implies(day == 1, end_time <= 450))  # Lawrence's constraint on Tuesday

    # Jesse's unavailable slots on Tuesday:
    # The meeting must not overlap with 0-30, 240-270, 300-360
    s.add(Implies(day == 1, Not(And(start_time < 30, end_time > 0))))  # overlaps 0-30
    s.add(Implies(day == 1, Not(And(start_time < 270, end_time > 240))))  # overlaps 240-270
    s.add(Implies(day == 1, Not(And(start_time < 360, end_time > 300))))  # overlaps 300-360

    # Lawrence's unavailable slots on Tuesday:
    # 30-90, 150-180, 240-270, 330-360, 390-450
    s.add(Implies(day == 1, Not(And(start_time < 90, end_time > 30))))  # overlaps 30-90
    s.add(Implies(day == 1, Not(And(start_time < 180, end_time > 150))))  # overlaps 150-180
    s.add(Implies(day == 1, Not(And(start_time < 270, end_time > 240))))  # overlaps 240-270
    s.add(Implies(day == 1, Not(And(start_time < 360, end_time > 330))))  # overlaps 330-360
    s.add(Implies(day == 1, Not(And(start_time < 450, end_time > 390))))  # overlaps 390-450

    # Now, find a time slot on Tuesday that is free for both
    # Possible slots are the gaps between their busy times:
    # For Jesse on Tuesday, free slots are:
    # 30-240, 270-300, 360-480 (but end_time <=450)
    # Lawrence's free slots on Tuesday:
    # 0-30 (but Jesse is busy 0-30), 90-150, 180-240, 270-330 (but 270-300 is free for Jesse, but Lawrence is free 270-330, but overlaps with 330-360 busy for Lawrence), 360-390 (Jesse is free, Lawrence is free), 450-480 (but end_time <=450)
    # So possible slots are 360-390 (since 360+30=390 <=450, and both are free)

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        day_val = model[day].as_long()
        start_val = model[start_time].as_long()
        end_val = model[end_time].as_long()

        # Determine the day
        day_str = "Monday" if day_val == 0 else "Tuesday"

        # Convert start and end times from minutes to HH:MM format
        start_hh = 9 + start_val // 60
        start_mm = start_val % 60
        end_hh = 9 + end_val // 60
        end_mm = end_val % 60

        # Format the times as two-digit strings
        start_time_str = f"{start_hh:02d}:{start_mm:02d}"
        end_time_str = f"{end_hh:02d}:{end_mm:02d}"

        # Print the solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling_problem()