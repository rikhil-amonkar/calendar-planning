from z3 import Solver, Int, Or, sat

def schedule_meeting():
    # Define the meeting start time in minutes from midnight.
    # Since work hours are 9:00 (540 minutes) to 17:00 (1020 minutes),
    # and the meeting lasts 60 minutes, we require meeting_start such that:
    # 540 <= meeting_start and meeting_start + 60 <= 1020.
    meeting_start = Int('meeting_start')
    meeting_duration = 60
    solver = Solver()
    solver.add(meeting_start >= 540, meeting_start + meeting_duration <= 1020)
    
    # Define the busy intervals (start, end) for each participant in minutes since midnight.
    # Danielle:
    #   9:00 - 10:00   => (540, 600)
    #   10:30 - 11:00  => (630, 660)
    #   14:30 - 15:00  => (870, 900)
    #   15:30 - 16:00  => (930, 960)
    #   16:30 - 17:00  => (990, 1020)
    # Bruce:
    #   11:00 - 11:30  => (660, 690)
    #   12:30 - 13:00  => (750, 780)
    #   14:00 - 14:30  => (840, 870)
    #   15:30 - 16:00  => (930, 960)
    # Eric:
    #   9:00 - 9:30    => (540, 570)
    #   10:00 - 11:00  => (600, 660)
    #   11:30 - 13:00  => (690, 780)
    #   14:30 - 15:30  => (870, 930)
    busy_intervals = [
        # Danielle's busy times
        (540, 600),
        (630, 660),
        (870, 900),
        (930, 960),
        (990, 1020),
        # Bruce's busy times
        (660, 690),
        (750, 780),
        (840, 870),
        (930, 960),
        # Eric's busy times
        (540, 570),
        (600, 660),
        (690, 780),
        (870, 930)
    ]
    
    # For each busy interval, ensure that the meeting does not overlap.
    # This is modeled by requiring:
    #   meeting_end <= busy_start OR meeting_start >= busy_end.
    for start_busy, end_busy in busy_intervals:
        solver.add(Or(meeting_start + meeting_duration <= start_busy,
                      meeting_start >= end_busy))
    
    if solver.check() == sat:
        model = solver.model()
        start = model[meeting_start].as_long()
        end = start + meeting_duration
        # Convert the times from minutes since midnight to HH:MM format.
        start_hour = start // 60
        start_min = start % 60
        end_hour = end // 60
        end_min = end % 60
        meeting_time = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
        print("Monday")
        print(meeting_time)
    else:
        print("No solution found.")

if __name__ == "__main__":
    schedule_meeting()