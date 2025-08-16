from z3 import *

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    # We represent time in minutes from midnight.
    # Work day is 9:00 (540 minutes) to 17:00 (1020 minutes).
    # Meeting duration is 30 minutes so start must be between 540 and 990.
    s = Int('s')
    solver = Solver()
    solver.add(s >= 540, s <= 990)

    # Busy intervals for each participant (start, end) in minutes.
    busy_intervals = [
        # Joan
        (690, 720),   # 11:30 - 12:00
        (870, 900),   # 14:30 - 15:00

        # Megan
        (540, 600),   # 9:00 - 10:00
        (840, 870),   # 14:00 - 14:30
        (960, 990),   # 16:00 - 16:30

        # Betty
        (570, 600),   # 9:30 - 10:00
        (690, 720),   # 11:30 - 12:00
        (810, 840),   # 13:30 - 14:00
        (960, 990),   # 16:00 - 16:30

        # Judith
        (540, 660),   # 9:00 - 11:00
        (720, 780),   # 12:00 - 13:00
        (840, 900),   # 14:00 - 15:00

        # Terry
        (570, 600),   # 9:30 - 10:00
        (690, 750),   # 11:30 - 12:30
        (780, 840),   # 13:00 - 14:00
        (900, 930),   # 15:00 - 15:30
        (960, 1020),  # 16:00 - 17:00

        # Kathryn
        (570, 600),   # 9:30 - 10:00
        (630, 660),   # 10:30 - 11:00
        (690, 780),   # 11:30 - 13:00
        (840, 960),   # 14:00 - 16:00
        (990, 1020)   # 16:30 - 17:00
    ]

    # For each busy interval, ensure the meeting [s, s+30] does not overlap.
    # The meeting is valid if it finishes by the busy interval start or starts after it finishes.
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(s + 30 <= busy_start, s >= busy_end))

    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[s].as_long()
        meeting_end = meeting_start + 30

        # Output the solution with the required format.
        print("SOLUTION:")
        print("Day: Monday")
        print("Start Time: " + minutes_to_time(meeting_start))
        print("End Time: " + minutes_to_time(meeting_end))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()