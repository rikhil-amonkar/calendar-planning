from z3 import Solver, Int, Or, sat

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

def main():
    # Meeting is 30 minutes long.
    # Represent time in minutes from midnight.
    # Work hours for Monday: 9:00 (540) to 17:00 (1020) but for a 30 minute meeting,
    # the meeting start must be at most 17:00 - 30 = 990.
    # However, since Jose doesn't want to meet after 15:30,
    # his constraint forces meeting_end <= 15:30 (i.e. meeting_start <= 15:00 (900)).
    # Thus we restrict meeting start m between 540 and 900.
    m = Int('m')  # meeting start time in minutes
    solver = Solver()
    solver.add(m >= 540, m <= 900)  # Domain constraint

    # Busy intervals for each participant (times in minutes from midnight)
    # Format: (busy start, busy end)
    busy_intervals = [
        # Jose's busy intervals
        (660, 690),  # 11:00 - 11:30
        (750, 780),  # 12:30 - 13:00

        # Keith's busy intervals
        (840, 870),  # 14:00 - 14:30
        (900, 930),  # 15:00 - 15:30

        # Logan's busy intervals
        (540, 600),  # 9:00  - 10:00
        (720, 750),  # 12:00 - 12:30
        (900, 930),  # 15:00 - 15:30

        # Megan's busy intervals
        (540, 630),  # 9:00  - 10:30
        (660, 720),  # 11:00 - 12:00
        (780, 810),  # 13:00 - 13:30
        (870, 990),  # 14:30 - 16:30

        # Gary's busy intervals
        (540, 570),  # 9:00  - 9:30
        (600, 630),  # 10:00 - 10:30
        (690, 780),  # 11:30 - 13:00
        (810, 840),  # 13:30 - 14:00
        (870, 990),  # 14:30 - 16:30

        # Bobby's busy intervals
        (660, 690),  # 11:00 - 11:30
        (720, 750),  # 12:00 - 12:30
        (780, 960)   # 13:00 - 16:00
    ]

    # For each busy interval, enforce that the meeting (m, m+30)
    # does not overlap with it.
    for start, end in busy_intervals:
        solver.add(Or(m + 30 <= start, m >= end))
    
    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[m].as_long()
        meeting_end = meeting_start + 30

        # Format the time strings in HH:MM (24-hour format)
        start_time_str = minutes_to_time(meeting_start)
        end_time_str = minutes_to_time(meeting_end)
        
        # According to the required output format:
        print("SOLUTION:")
        print("Day: Monday")
        print("Start Time: " + start_time_str)
        print("End Time: " + end_time_str)
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()