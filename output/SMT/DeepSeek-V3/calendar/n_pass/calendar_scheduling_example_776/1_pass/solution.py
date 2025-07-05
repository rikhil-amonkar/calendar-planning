from z3 import *

def solve_scheduling():
    # Create solver instance
    s = Solver()

    # Define possible days (0: Monday, 1: Tuesday, 2: Wednesday)
    day = Int('day')
    s.add(day >= 0, day <= 2)

    # Define start time in minutes from 9:00 (540 minutes since 9*60=540)
    start_time = Int('start_time')
    s.add(start_time >= 540, start_time <= 1020 - 30)  # 17:00 is 1020 minutes, meeting duration 30 minutes

    # Jennifer's busy times for each day in minutes since 9:00
    # Each entry is (start, end) in minutes from 9:00
    jennifer_busy = {
        0: [(0, 120), (150, 240), (270, 330), (360, 480)],  # Monday: 9-11, 11:30-13, 13:30-14:30, 15-17
        1: [(0, 150), (180, 480)],  # Tuesday: 9-11:30, 12-17
        2: [(0, 150), (180, 210), (240, 300), (330, 420), (450, 480)]  # Wednesday: 9-11:30, 12-12:30, 13-14, 14:30-16, 16:30-17
    }

    # John's preferences: avoid Monday after 14:30 (870 minutes from midnight, 870 - 540 = 330 minutes from 9:00)
    # Also avoid Tuesday and Wednesday (day 1 and 2)
    # So we prefer day 0 (Monday) with start_time +30 <= 870 (i.e., start_time <= 840)
    # But since John's entire week is free, his preference is just to avoid those times if possible.

    # For each possible day, the meeting must not overlap with Jennifer's busy times
    # Also, the meeting is 30 minutes long, so start_time +30 <= end_time of any busy slot or outside busy slots

    # Function to check if a time interval (s, s+30) overlaps with any busy interval in the given day
    def is_available(day_val, s_time):
        busy_intervals = jennifer_busy.get(day_val, [])
        for (busy_start, busy_end) in busy_intervals:
            if Not(Or(s_time >= busy_end, s_time + 30 <= busy_start)):
                return False
        return True

    # Z3 constraints for meeting not overlapping with Jennifer's busy times
    day_val = day
    s.add(Or(
        And(day_val == 0, 
            Or(
                And(start_time >= 0, start_time + 30 <= 120),
                And(start_time >= 120, start_time + 30 <= 150),
                And(start_time >= 240, start_time + 30 <= 270),
                And(start_time >= 330, start_time + 30 <= 360),
                And(start_time >= 480, start_time + 30 <= 540)  # beyond 17:00? No, since 17:00 is 480 minutes from 9:00 (540 + 480=1020 minutes from midnight)
            )),
        And(day_val == 1,
            Or(
                And(start_time >= 150, start_time + 30 <= 180)
            )),
        And(day_val == 2,
            Or(
                And(start_time >= 150, start_time + 30 <= 180),
                And(start_time >= 210, start_time + 30 <= 240),
                And(start_time >= 300, start_time + 30 <= 330),
                And(start_time >= 420, start_time + 30 <= 450),
                And(start_time >= 480, start_time + 30 <= 540)  # again, beyond 17:00 is invalid
            ))
    ))

    # Also, the meeting must end by 17:00 (1020 minutes from midnight, 480 from 9:00)
    s.add(start_time + 30 <= 480)

    # John's preferences: avoid Monday after 14:30 (330 minutes from 9:00 is 14:30, so start_time +30 <= 330)
    # Also avoid Tuesday and Wednesday. So we can add soft constraints, but Z3 doesn't handle preferences directly.
    # So first try to find a solution on Monday before 14:30, then other times.

    # We'll use a check with multiple possible constraints, prioritizing preferred times.

    # First, try to find a solution on Monday before 14:30 (start_time +30 <= 330)
    temp_solver = Solver()
    temp_solver.add(s.assertions())
    temp_solver.add(day == 0)
    temp_solver.add(start_time + 30 <= 330)
    if temp_solver.check() == sat:
        m = temp_solver.model()
        day_sol = m[day].as_long()
        start_sol = m[start_time].as_long()
        end_sol = start_sol + 30
    else:
        # If no solution on Monday before 14:30, try any other day
        if s.check() == sat:
            m = s.model()
            day_sol = m[day].as_long()
            start_sol = m[start_time].as_long()
            end_sol = start_sol + 30
        else:
            return "No solution found"

    # Convert day number to day name
    days = ["Monday", "Tuesday", "Wednesday"]
    day_name = days[day_sol]

    # Convert start and end times from minutes since 9:00 to HH:MM
    def minutes_to_time(minutes):
        total_minutes = 540 + minutes  # 9:00 is 540 minutes from midnight
        h = total_minutes // 60
        m = total_minutes % 60
        return f"{h:02d}:{m:02d}"

    start_time_str = minutes_to_time(start_sol)
    end_time_str = minutes_to_time(end_sol)

    # Prepare the solution output
    solution = f"SOLUTION:\nDay: {day_name}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}"
    return solution

print(solve_scheduling())