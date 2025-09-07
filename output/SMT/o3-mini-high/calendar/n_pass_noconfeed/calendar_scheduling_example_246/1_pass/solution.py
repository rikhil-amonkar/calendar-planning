from z3 import Solver, Int, Or, sat

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    # Meeting duration: 30 minutes
    meeting_duration = 30
    # Workday bounds in minutes since midnight (9:00 to 17:00)
    start_bound = 9 * 60     # 540 minutes -> 09:00
    end_bound   = 17 * 60    # 1020 minutes -> 17:00
    latest_start = end_bound - meeting_duration  # Meeting must end by 17:00

    # Define the meeting start time variable (in minutes since midnight)
    meeting_start = Int('meeting_start')

    solver = Solver()
    # Meeting must start within work hours (meeting_end = meeting_start+30 <= 1020)
    solver.add(meeting_start >= start_bound, meeting_start <= latest_start)

    # Busy intervals for each participant (times in minutes since midnight)
    # Jacob's busy times: 13:30-14:00 and 14:30-15:00
    # Diana's busy times: 9:30-10:00, 11:30-12:00, 13:00-13:30, 16:00-16:30
    # Adam's busy times: 9:30-10:30, 11:00-12:30, 15:30-16:00
    # Angela's busy times: 9:30-10:00, 10:30-12:00, 13:00-15:30, 16:00-16:30
    # Dennis's busy times: 9:00-9:30, 10:30-11:30, 13:00-15:00, 16:30-17:00
    busy_intervals = [
        # Jacob
        (13 * 60 + 30, 14 * 60),    # 13:30 to 14:00   -> (810, 840)
        (14 * 60 + 30, 15 * 60),    # 14:30 to 15:00   -> (870, 900)
        # Diana
        (9 * 60 + 30, 10 * 60),     # 09:30 to 10:00   -> (570, 600)
        (11 * 60 + 30, 12 * 60),    # 11:30 to 12:00   -> (690, 720)
        (13 * 60, 13 * 60 + 30),    # 13:00 to 13:30   -> (780, 810)
        (16 * 60, 16 * 60 + 30),    # 16:00 to 16:30   -> (960, 990)
        # Adam
        (9 * 60 + 30, 10 * 60 + 30), # 09:30 to 10:30  -> (570, 630)
        (11 * 60, 12 * 60 + 30),     # 11:00 to 12:30  -> (660, 750)
        (15 * 60 + 30, 16 * 60),     # 15:30 to 16:00  -> (930, 960)
        # Angela
        (9 * 60 + 30, 10 * 60),      # 09:30 to 10:00  -> (570, 600)
        (10 * 60 + 30, 12 * 60),     # 10:30 to 12:00  -> (630, 720)
        (13 * 60, 15 * 60 + 30),     # 13:00 to 15:30  -> (780, 930)
        (16 * 60, 16 * 60 + 30),     # 16:00 to 16:30  -> (960, 990)
        # Dennis
        (9 * 60, 9 * 60 + 30),       # 09:00 to 09:30  -> (540, 570)
        (10 * 60 + 30, 11 * 60 + 30), # 10:30 to 11:30  -> (630, 690)
        (13 * 60, 15 * 60),          # 13:00 to 15:00  -> (780, 900)
        (16 * 60 + 30, 17 * 60)      # 16:30 to 17:00  -> (990, 1020)
    ]

    # For each busy interval, add a constraint that the meeting does not overlap with it.
    # A meeting (from meeting_start to meeting_start+meeting_duration) does not overlap
    # with a busy interval (busy_start, busy_end) if either it ends before the busy interval starts 
    # or it starts after the busy interval ends.
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(meeting_start + meeting_duration <= busy_start, meeting_start >= busy_end))

    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        start_val = model[meeting_start].as_long()
        end_val = start_val + meeting_duration

        start_str = format_time(start_val)
        end_str = format_time(end_val)

        # Output the meeting time and day of the week in the required format.
        # Example output: Monday, {12:30:13:00}
        print(f"Monday, {{{start_str}:{end_str}}}")
    else:
        print("No valid meeting time found.")

if __name__ == "__main__":
    main()