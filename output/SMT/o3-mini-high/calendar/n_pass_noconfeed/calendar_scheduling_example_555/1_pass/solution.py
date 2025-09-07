from z3 import Solver, Int, Or, sat

def main():
    # Define meeting duration in minutes
    meeting_duration = 30

    # Create a solver instance
    s = Solver()

    # Represent meeting start time in minutes after midnight on Monday.
    meeting_start = Int("meeting_start")
    meeting_end = meeting_start + meeting_duration

    # Working hours: meeting can only be scheduled between 9:00 (540) and 17:00 (1020)
    s.add(meeting_start >= 9 * 60)        # 9:00 -> 540 minutes
    s.add(meeting_end <= 17 * 60)         # 17:00 -> 1020 minutes

    # Evelyn's constraint: Do not want to meet after 13:00 (i.e. meeting must end by 13:00 (780))
    s.add(meeting_end <= 13 * 60)         # 13:00 -> 780 minutes

    # Randy's blocked time intervals (in minutes):
    # Block 1: 9:00 to 10:30 -> [540, 630]
    # Block 2: 11:00 to 15:30 -> [660, 930]
    # Block 3: 16:00 to 17:00 -> [960, 1020]
    # For each block, meeting must not overlap; i.e. meeting_end <= block_start OR meeting_start >= block_end.

    # Block 1
    s.add(Or(meeting_end <= 540, meeting_start >= 630))
    # Block 2
    s.add(Or(meeting_end <= 660, meeting_start >= 930))
    # Block 3
    s.add(Or(meeting_end <= 960, meeting_start >= 1020))

    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        start_val = m[meeting_start].as_long()
        end_val = start_val + meeting_duration

        # Convert minutes into HH:MM format
        start_hour = start_val // 60
        start_minute = start_val % 60
        end_hour = end_val // 60
        end_minute = end_val % 60

        # Output meeting time in the format HH:MM:HH:MM along with the day of the week
        print(f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d} Monday")
    else:
        print("No solution exists.")

if __name__ == "__main__":
    main()