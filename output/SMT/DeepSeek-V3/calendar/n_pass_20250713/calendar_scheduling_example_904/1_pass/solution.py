from z3 import *

def solve_scheduling():
    # Create solver instance
    s = Solver()

    # Define the days and work hours
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes

    # Variables for the meeting day and start time
    day = Int('day')  # 0: Monday, 1: Tuesday, ..., 4: Friday
    start_time = Int('start_time')  # in minutes from 0 (00:00)

    # Constraint: day must be between 0 and 4 (Monday to Friday)
    s.add(day >= 0, day <= 4)

    # Constraint: start time must be within work hours and leave room for 30-minute meeting
    s.add(start_time >= work_start, start_time + 30 <= work_end)

    # Daniel's busy slots (day, start, end in minutes)
    daniel_busy = [
        (0, 9*60 + 30, 10*60 + 30), (0, 12*60, 12*60 + 30), (0, 13*60, 14*60),
        (0, 14*60 + 30, 15*60), (0, 15*60 + 30, 16*60),
        (1, 11*60, 12*60), (1, 13*60, 13*60 + 30), (1, 15*60 + 30, 16*60), (1, 16*60 + 30, 17*60),
        (2, 9*60, 10*60), (2, 14*60, 14*60 + 30),
        (3, 10*60 + 30, 11*60), (3, 12*60, 13*60), (3, 14*60 + 30, 15*60), (3, 15*60 + 30, 16*60),
        (4, 9*60, 9*60 + 30), (4, 11*60 + 30, 12*60), (4, 13*60, 13*60 + 30), (4, 16*60 + 30, 17*60)
    ]

    # Bradley's busy slots (day, start, end in minutes)
    bradley_busy = [
        (0, 9*60 + 30, 11*60), (0, 11*60 + 30, 12*60), (0, 12*60 + 30, 13*60), (0, 14*60, 15*60),
        (1, 10*60 + 30, 11*60), (1, 12*60, 13*60), (1, 13*60 + 30, 14*60), (1, 15*60 + 30, 16*60 + 30),
        (2, 9*60, 10*60), (2, 11*60, 13*60), (2, 13*60 + 30, 14*60), (2, 14*60 + 30, 17*60),
        (3, 9*60, 12*60 + 30), (3, 13*60 + 30, 14*60), (3, 14*60 + 30, 15*60), (3, 15*60 + 30, 16*60 + 30),
        (4, 9*60, 9*60 + 30), (4, 10*60, 12*60 + 30), (4, 13*60, 13*60 + 30), (4, 14*60, 14*60 + 30), (4, 15*60 + 30, 16*60 + 30)
    ]

    # Constraints for Daniel's busy slots
    for d, start, end in daniel_busy:
        s.add(Not(And(day == d, start_time < end, start_time + 30 > start)))

    # Constraints for Bradley's busy slots
    for d, start, end in bradley_busy:
        s.add(Not(And(day == d, start_time < end, start_time + 30 > start)))

    # Preferences:
    # Daniel would rather not meet on Wednesday, Thursday
    s.add(day != 2, day != 3)
    # Bradley does not want to meet on Monday, Tuesday before 12:00, Friday
    s.add(day != 0)
    s.add(Not(And(day == 1, start_time < 12 * 60)))
    s.add(day != 4)

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        day_idx = m[day].as_long()
        start_min = m[start_time].as_long()
        end_min = start_min + 30

        # Convert minutes to HH:MM format
        start_hh = start_min // 60
        start_mm = start_min % 60
        end_hh = end_min // 60
        end_mm = end_min % 60

        # Format the output
        solution = f"SOLUTION:\nDay: {days[day_idx]}\nStart Time: {start_hh:02d}:{start_mm:02d}\nEnd Time: {end_hh:02d}:{end_mm:02d}"
        print(solution)
    else:
        print("No solution found")

solve_scheduling()