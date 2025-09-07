from z3 import *

def main():
    # Create a solver instance.
    solver = Solver()

    # Define variables:
    # s: meeting start time in minutes after midnight.
    # d: day of the meeting (0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday)
    s = Int('s')
    d = Int('d')

    # Working hours are 9:00 (540 minutes) to 17:00 (1020 minutes). 
    # The meeting is 60 minutes long so s + 60 must be <= 1020.
    solver.add(s >= 540, s + 60 <= 1020)
    solver.add(d >= 0, d <= 4)

    # Busy intervals for each participant.
    # Each tuple is (day, busy_start, busy_end), where times are in minutes after midnight.
    busy_intervals = [
        # Diane's busy times
        # Monday (day 0)
        (0, 720, 750),   # 12:00 - 12:30
        (0, 900, 930),   # 15:00 - 15:30
        # Tuesday (day 1)
        (1, 600, 660),   # 10:00 - 11:00
        (1, 690, 720),   # 11:30 - 12:00
        (1, 750, 780),   # 12:30 - 13:00
        (1, 960, 1020),  # 16:00 - 17:00
        # Wednesday (day 2)
        (2, 540, 570),   # 9:00 - 9:30
        (2, 870, 900),   # 14:30 - 15:00
        (2, 990, 1020),  # 16:30 - 17:00
        # Thursday (day 3)
        (3, 930, 990),   # 15:30 - 16:30
        # Friday (day 4)
        (4, 570, 690),   # 9:30 - 11:30
        (4, 870, 900),   # 14:30 - 15:00
        (4, 960, 1020),  # 16:00 - 17:00

        # Matthew's busy times
        # Monday (day 0)
        (0, 540, 600),   # 9:00 - 10:00
        (0, 630, 1020),  # 10:30 - 17:00
        # Tuesday (day 1)
        (1, 540, 1020),  # 9:00 - 17:00
        # Wednesday (day 2)
        (2, 540, 660),   # 9:00 - 11:00
        (2, 720, 870),   # 12:00 - 14:30
        (2, 960, 1020),  # 16:00 - 17:00
        # Thursday (day 3)
        (3, 540, 960),   # 9:00 - 16:00
        # Friday (day 4)
        (4, 540, 1020)   # 9:00 - 17:00
    ]

    # For each busy interval, add a constraint stating:
    # "Either the meeting is not on that day,
    #  or the meeting ends before the busy interval starts,
    #  or it begins after the busy interval ends."
    for (day_val, busy_start, busy_end) in busy_intervals:
        solver.add(Or(d != day_val, s + 60 <= busy_start, s >= busy_end))

    # Matthew's time preference: he would rather not meet on Wednesday before 12:30.
    # That is, if the meeting is on Wednesday (d == 2), then it must start at or after 12:30 (750 minutes).
    solver.add(Implies(d == 2, s >= 750))

    # Check if the constraints are satisfiable.
    if solver.check() == sat:
        model = solver.model()
        meeting_day = model[d].as_long()
        meeting_start = model[s].as_long()
        meeting_end = meeting_start + 60

        # Map day indices to day names.
        day_names = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        day_name = day_names[meeting_day]

        # Convert meeting start and end times into HH:MM format.
        start_hour = meeting_start // 60
        start_minute = meeting_start % 60
        end_hour = meeting_end // 60
        end_minute = meeting_end % 60

        # Format the time range as HH:MM:HH:MM.
        time_range = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"

        # Output the day and the meeting time.
        print(day_name, time_range)
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()