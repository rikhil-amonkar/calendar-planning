from z3 import *

def solve_scheduling_problem():
    # Create solver instance
    s = Solver()

    # Define possible days (0: Monday, 1: Tuesday, 2: Wednesday)
    day = Int('day')
    s.add(day >= 0, day <= 2)  # Monday, Tuesday, or Wednesday

    # Define start time in minutes from 9:00 (540 minutes)
    start_time = Int('start_time')
    s.add(start_time >= 540, start_time <= 1020 - 30)  # 17:00 is 1020 minutes, meeting is 30 mins

    # Convert start_time to HH:MM format for constraints
    def time_to_hhmm(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return hh, mm

    # Cheryl cannot meet on Wednesday (day 2)
    s.add(day != 2)

    # Define busy times for Cheryl and Kyle
    # Each busy time is (day, start_min, end_min)
    cheryl_busy = [
        (0, 540, 570),   # Monday 9:00-9:30
        (0, 690, 780),    # Monday 11:30-13:00
        (0, 930, 960),    # Monday 15:30-16:00
        (1, 900, 930),    # Tuesday 15:00-15:30
    ]

    kyle_busy = [
        (0, 540, 1020),   # Monday 9:00-17:00
        (1, 570, 1020),   # Tuesday 9:30-17:00
        (2, 540, 570),     # Wednesday 9:00-9:30
        (2, 600, 780),     # Wednesday 10:00-13:00
        (2, 810, 840),     # Wednesday 13:30-14:00
        (2, 870, 1020),    # Wednesday 14:30-17:00
    ]

    # Add constraints that the meeting does not overlap with busy times
    meeting_end = start_time + 30

    # For Cheryl's busy times
    for (busy_day, busy_start, busy_end) in cheryl_busy:
        s.add(Not(And(day == busy_day,
                      Or(And(start_time >= busy_start, start_time < busy_end),
                         And(meeting_end > busy_start, meeting_end <= busy_end),
                         And(start_time <= busy_start, meeting_end >= busy_end)))))

    # For Kyle's busy times
    for (busy_day, busy_start, busy_end) in kyle_busy:
        s.add(Not(And(day == busy_day,
                      Or(And(start_time >= busy_start, start_time < busy_end),
                         And(meeting_end > busy_start, meeting_end <= busy_end),
                         And(start_time <= busy_start, meeting_end >= busy_end)))))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_min = m[start_time].as_long()

        # Convert day and time to required format
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[day_val]

        hh = start_min // 60
        mm = start_min % 60
        start_str = f"{hh:02d}:{mm:02d}"

        end_min = start_min + 30
        hh = end_min // 60
        mm = end_min % 60
        end_str = f"{hh:02d}:{mm:02d}"

        # Print the solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

solve_scheduling_problem()