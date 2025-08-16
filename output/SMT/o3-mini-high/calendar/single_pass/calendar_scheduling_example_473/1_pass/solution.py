from z3 import *

def main():
    # Define the meeting duration (in minutes)
    meeting_duration = 30

    # Define an integer variable for the meeting's start time (in minutes after midnight)
    meeting_start = Int('meeting_start')
    meeting_end = meeting_start + meeting_duration

    solver = Solver()

    # Workday is from 9:00 (540 minutes) to 17:00 (1020 minutes)
    solver.add(meeting_start >= 540)       # Meeting cannot start before 9:00
    solver.add(meeting_end <= 1020)          # Meeting must end by 17:00

    # Busy intervals for each participant (all times in minutes)
    # Format: (start, end)
    busy_intervals = [
        # Gregory
        (540, 570),    # 9:00 - 9:30
        (690, 720),    # 11:30 - 12:00

        # Jonathan
        (540, 570),    # 9:00 - 9:30
        (720, 750),    # 12:00 - 12:30
        (780, 810),    # 13:00 - 13:30
        (900, 960),    # 15:00 - 16:00
        (990, 1020),   # 16:30 - 17:00

        # Barbara
        (600, 630),    # 10:00 - 10:30
        (810, 840),    # 13:30 - 14:00

        # Jesse
        (600, 660),    # 10:00 - 11:00
        (750, 870),    # 12:30 - 14:30

        # Alan
        (570, 660),    # 9:30 - 11:00
        (690, 750),    # 11:30 - 12:30
        (780, 930),    # 13:00 - 15:30
        (960, 1020),   # 16:00 - 17:00

        # Nicole
        (540, 630),    # 9:00 - 10:30
        (690, 720),    # 11:30 - 12:00
        (750, 810),    # 12:30 - 13:30
        (840, 1020),   # 14:00 - 17:00

        # Catherine
        (540, 630),    # 9:00 - 10:30
        (720, 810),    # 12:00 - 13:30
        (900, 930),    # 15:00 - 15:30
        (960, 990)     # 16:00 - 16:30
    ]

    # Ensure that the meeting does not overlap any busy interval.
    # For each busy interval the meeting must either finish before it starts or start after it ends.
    for (busy_start, busy_end) in busy_intervals:
        solver.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))

    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        start = model[meeting_start].as_long()
        end = start + meeting_duration

        # Convert the start and end times from minutes to HH:MM format
        start_hour = start // 60
        start_minute = start % 60
        end_hour = end // 60
        end_minute = end % 60

        print("SOLUTION:")
        print("Day: Monday")
        print("Start Time: {0:02d}:{1:02d}".format(start_hour, start_minute))
        print("End Time: {0:02d}:{1:02d}".format(end_hour, end_minute))
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()