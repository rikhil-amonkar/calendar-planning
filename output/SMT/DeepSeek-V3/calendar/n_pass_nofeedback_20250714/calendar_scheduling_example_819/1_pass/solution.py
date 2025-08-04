from z3 import *

def solve_scheduling():
    # Create solver instance
    s = Solver()

    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday
    start_time = Int('start_time')  # in minutes from 9:00 (e.g., 0 is 9:00, 30 is 9:30)

    # Meeting duration is fixed to 30 minutes
    duration = 30

    # Possible days: Monday (0), Tuesday (1), Wednesday (2), Thursday (3)
    s.add(day >= 0, day <= 3)

    # Work hours are 9:00 to 17:00 (480 minutes from 9:00)
    s.add(start_time >= 0, start_time + duration <= 480)

    # Julie's constraints: no meetings on Thursday before 11:30 (i.e., 9:00 to 11:30 is 0 to 150 minutes)
    # So if day is Thursday, start_time must not be < 150 minutes (11:30 - 9:00 = 2.5 hours = 150 minutes)
    s.add(Implies(day == 3, start_time >= 150))

    # Ruth's constraints:
    # Monday, Tuesday, Wednesday: all day busy (9:00-17:00)
    # So meeting can't be on these days
    s.add(day != 0)
    s.add(day != 1)
    s.add(day != 2)

    # On Thursday:
    # Ruth is busy during 9:00-11:00 (0-120), 11:30-14:30 (150-330), 15:00-17:00 (360-480)
    # Available slots: 11:00-11:30 (120-150), 14:30-15:00 (330-360)
    # So the meeting must fit into one of these slots:
    # Option 1: start_time >= 120 and start_time + duration <= 150
    # Option 2: start_time >= 330 and start_time + duration <= 360
    s.add(Or(
        And(day == 3, start_time >= 120, start_time + duration <= 150),
        And(day == 3, start_time >= 330, start_time + duration <= 360)
    ))

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_time_val = m[start_time].as_long()

        # Convert day to string
        days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
        day_str = days[day_val]

        # Calculate start and end times in HH:MM format
        start_hour = 9 + start_time_val // 60
        start_minute = start_time_val % 60
        end_time_val = start_time_val + duration
        end_hour = 9 + end_time_val // 60
        end_minute = end_time_val % 60

        # Format times as HH:MM
        start_time_str = f"{start_hour:02d}:{start_minute:02d}"
        end_time_str = f"{end_hour:02d}:{end_minute:02d}"

        # Print the solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()