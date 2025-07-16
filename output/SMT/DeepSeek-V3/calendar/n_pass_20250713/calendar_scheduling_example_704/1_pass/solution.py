from z3 import *

def solve_scheduling():
    # Create solver instance
    s = Solver()

    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday
    start_time = Int('start_time')  # in minutes from 9:00 (e.g., 0 is 9:00, 30 is 9:30)
    end_time = Int('end_time')

    # Meeting duration is 30 minutes
    s.add(end_time == start_time + 30)

    # Work hours are 9:00 to 17:00 (0 to 480 minutes)
    s.add(start_time >= 0)
    s.add(end_time <= 480)

    # Day must be 0, 1, or 2
    s.add(day >= 0)
    s.add(day <= 2)

    # Larry's calendar is wide open, no constraints except day preference (not Wednesday)
    s.add(day != 2)  # Larry prefers not Wednesday

    # Samuel's constraints based on day
    # Monday (day 0): Samuel's meetings: 10:30-11:00 (90-120), 12:00-12:30 (180-210), 13:00-15:00 (240-360), 15:30-16:30 (390-450)
    monday_constraints = Or(
        And(day != 0),
        And(day == 0,
            Or(
                end_time <= 90,   # Before 10:30
                And(start_time >= 120, end_time <= 180),   # 11:00-12:00
                And(start_time >= 210, end_time <= 240),   # 12:30-13:00
                And(start_time >= 360, end_time <= 390),   # 15:00-15:30
                start_time >= 450   # After 16:30
            )
        )
    )

    # Tuesday (day 1): Samuel's meetings: 9:00-12:00 (0-180), 14:00-15:30 (300-390), 16:30-17:00 (450-480)
    tuesday_constraints = Or(
        And(day != 1),
        And(day == 1,
            Or(
                And(start_time >= 180, end_time <= 300),   # 12:00-14:00
                And(start_time >= 390, end_time <= 450)    # 15:30-16:30
            )
        )
    )

    # Wednesday (day 2): Samuel's meetings: 10:30-11:00 (90-120), 11:30-12:00 (150-180), 12:30-13:00 (210-240), 14:00-14:30 (300-330), 15:00-16:00 (360-420)
    wednesday_constraints = Or(
        And(day != 2),
        And(day == 2,
            Or(
                end_time <= 90,   # Before 10:30
                And(start_time >= 120, end_time <= 150),   # 11:00-11:30
                And(start_time >= 180, end_time <= 210),   # 12:00-12:30
                And(start_time >= 240, end_time <= 300),    # 13:00-14:00
                And(start_time >= 330, end_time <= 360),    # 14:30-15:00
                start_time >= 420   # After 16:00
            )
        )
    )

    s.add(monday_constraints)
    s.add(tuesday_constraints)
    s.add(wednesday_constraints)

    # Samuel prefers to avoid more meetings on Tuesday (day 1), so prioritize other days
    # To model this, we first try to find solutions where day is not 1, then if no solution, allow day 1
    # We'll use a custom strategy to find the earliest possible time on the earliest possible day
    # We'll check days in order 0, 1, 2 and find the earliest start time

    # Check Monday first
    temp_solver = Solver()
    temp_solver.add(s.assertions())
    temp_solver.add(day == 0)
    if temp_solver.check() == sat:
        model = temp_solver.model()
        best_day = 0
        best_start = model.eval(start_time).as_long()
    else:
        # Check Tuesday next
        temp_solver = Solver()
        temp_solver.add(s.assertions())
        temp_solver.add(day == 1)
        if temp_solver.check() == sat:
            model = temp_solver.model()
            best_day = 1
            best_start = model.eval(start_time).as_long()
        else:
            # Check Wednesday
            temp_solver = Solver()
            temp_solver.add(s.assertions())
            temp_solver.add(day == 2)
            if temp_solver.check() == sat:
                model = temp_solver.model()
                best_day = 2
                best_start = model.eval(start_time).as_long()
            else:
                return "No solution found"

    # Now, find the earliest start time on the best_day
    temp_solver = Solver()
    temp_solver.add(s.assertions())
    temp_solver.add(day == best_day)
    # To find the earliest start time, we minimize start_time
    temp_solver.minimize(start_time)
    if temp_solver.check() == sat:
        model = temp_solver.model()
        best_day = model.eval(day).as_long()
        best_start = model.eval(start_time).as_long()
        best_end = model.eval(end_time).as_long()

        # Convert day to string
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[best_day]

        # Convert start and end times to HH:MM format
        start_hour = 9 + best_start // 60
        start_min = best_start % 60
        end_hour = 9 + best_end // 60
        end_min = best_end % 60

        start_time_str = f"{start_hour:02d}:{start_min:02d}"
        end_time_str = f"{end_hour:02d}:{end_min:02d}"

        return f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}"
    else:
        return "No solution found"

print(solve_scheduling())