from z3 import *

def solve_scheduling():
    # Create solver instance
    s = Solver()

    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday
    start_time = Int('start_time')  # minutes from 9:00
    end_time = Int('end_time')

    # Day must be Monday (0), Tuesday (1), or Wednesday (2)
    s.add(day >= 0, day <= 2)

    # Meeting duration is exactly 30 minutes
    s.add(end_time == start_time + 30)

    # Meeting must be within 9:00-17:00 (0-480 minutes)
    s.add(start_time >= 0)
    s.add(end_time <= 480)

    # Amy's busy times (only Wednesday)
    # Wednesday 11:00-11:30 (120-150), 13:30-14:00 (270-300)
    s.add(Not(And(day == 2,
                  Or(And(start_time < 150, end_time > 120),
                     And(start_time < 300, end_time > 270))))

    # Pamela's busy times
    # Monday: 9:00-10:30 (0-90), 11:00-16:30 (120-450)
    s.add(Not(And(day == 0,
                  Or(And(start_time < 90, end_time > 0),
                     And(start_time < 450, end_time > 120))))

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

    # Pamela's preferences
    s.add(day != 0)  # No meetings on Monday
    # On Tuesday/Wednesday, only after 16:00 (420 minutes)
    s.add(Implies(Or(day == 1, day == 2), start_time >= 420)

    # Check for solution
    if s.check() == sat:
        model = s.model()
        day_val = model[day].as_long()
        start_val = model[start_time].as_long()
        end_val = model[end_time].as_long()

        # Convert to readable format
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[day_val]
        
        start_hh = 9 + start_val // 60
        start_mm = start_val % 60
        end_hh = 9 + end_val // 60
        end_mm = end_val % 60

        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
        print(f"End Time: {end_hh:02d}:{end_mm:02d}")
    else:
        print("No solution found")

solve_scheduling()