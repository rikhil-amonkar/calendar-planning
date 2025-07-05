from z3 import *

def solve_scheduling():
    # Create solver instance
    s = Solver()

    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday
    start_time = Int('start_time')  # in minutes from 9:00 (e.g., 0 is 9:00, 60 is 10:00)
    end_time = Int('end_time')

    # Possible days: Monday (0), Tuesday (1), Wednesday (2)
    s.add(day >= 0, day <= 2)

    # Meeting duration is 30 minutes
    s.add(end_time == start_time + 30)

    # Meeting must be within 9:00 to 17:00 (0 to 480 minutes)
    s.add(start_time >= 0)
    s.add(end_time <= 480)  # 17:00 is 8 hours after 9:00 (8*60=480)

    # Amy's busy times (converted to minutes from 9:00)
    # Wednesday: 11:00-11:30 (120-150), 13:30-14:00 (270-300)
    # So on Wednesday (day 2), the meeting cannot overlap with these intervals
    # For Amy, constraints are only for Wednesday
    s.add(Not(And(day == 2,
                  Or(And(start_time < 150, end_time > 120),  # overlaps 11:00-11:30
                     And(start_time < 300, end_time > 270)))))  # overlaps 13:30-14:00

    # Pamela's busy times:
    # Monday: 9:00-10:30 (0-90), 11:00-16:30 (120-450)
    # So on Monday (day 0), the meeting cannot overlap with these intervals
    s.add(Not(And(day == 0,
                  Or(And(start_time < 90, end_time > 0),
                     And(start_time < 450, end_time > 120)))))

    # Tuesday: 9:00-9:30 (0-30), 10:00-17:00 (60-480)
    s.add(Not(And(day == 1,
                  Or(And(start_time < 30, end_time > 0),
                     And(start_time < 480, end_time > 60)))))

    # Wednesday: 9:00-9:30 (0-30), 10:00-11:00 (60-120), 11:30-13:30 (150-270), 14:30-15:00 (330-360), 16:00-16:30 (420-450)
    s.add(Not(And(day == 2,
                  Or(And(start_time < 30, end_time > 0),
                     And(start_time < 120, end_time > 60),
                     And(start_time < 270, end_time > 150),
                     And(start_time < 360, end_time > 330),
                     And(start_time < 450, end_time > 420)))))

    # Pamela's preferences: avoid more meetings on Monday (so day cannot be 0)
    s.add(day != 0)
    # On Tuesday or Wednesday, start time must be >= 420 (16:00)
    s.add(Implies(Or(day == 1, day == 2), start_time >= 420)

    # Check for a solution
    if s.check() == sat:
        model = s.model()
        day_val = model[day].as_long()
        start_val = model[start_time].as_long()
        end_val = model[end_time].as_long()

        # Convert day to string
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[day_val]

        # Convert start and end times to HH:MM format
        start_hh = 9 + start_val // 60
        start_mm = start_val % 60
        end_hh = 9 + end_val // 60
        end_mm = end_val % 60

        # Format as two-digit strings
        start_time_str = f"{start_hh:02d}:{start_mm:02d}"
        end_time_str = f"{end_hh:02d}:{end_mm:02d}"

        # Print the solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()