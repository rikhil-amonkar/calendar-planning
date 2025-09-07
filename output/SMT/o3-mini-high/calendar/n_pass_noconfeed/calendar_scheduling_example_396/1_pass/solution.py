from z3 import *

def minutes_to_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02}:{minutes:02}"

def main():
    # Convert times to minutes from midnight.
    work_start = 9 * 60      # 9:00 -> 540
    work_end = 17 * 60       # 17:00 -> 1020
    duration = 30            # meeting duration in minutes

    # Define the meeting start time as an integer variable (in minutes)
    meeting_start = Int('meeting_start')
    meeting_end = meeting_start + duration

    # Create a solver instance
    s = Solver()

    # Meeting must be scheduled completely within working hours.
    s.add(meeting_start >= work_start, meeting_end <= work_end)

    # Define a helper predicate for ensuring the meeting does not overlap a busy interval.
    # For a busy interval [busy_start, busy_end), the meeting should either end before busy_start or start after busy_end.
    def no_overlap(busy_start, busy_end):
        return Or(meeting_end <= busy_start, meeting_start >= busy_end)

    # Busy intervals for each participant (times in minutes from midnight):
    busy_intervals = [
        # Jack's busy times: 9:00-9:30 and 14:00-14:30
        (9 * 60, 9 * 60 + 30),
        (14 * 60, 14 * 60 + 30),

        # Madison's busy times: 9:30-10:30, 13:00-14:00, 15:00-15:30, and 16:30-17:00
        (9 * 60 + 30, 10 * 60 + 30),
        (13 * 60, 14 * 60),
        (15 * 60, 15 * 60 + 30),
        (16 * 60 + 30, 17 * 60),

        # Rachel's busy times: 9:30-10:30, 11:00-11:30, 12:00-13:30, 14:30-15:30 and 16:00-17:00
        (9 * 60 + 30, 10 * 60 + 30),
        (11 * 60, 11 * 60 + 30),
        (12 * 60, 13 * 60 + 30),
        (14 * 60 + 30, 15 * 60 + 30),
        (16 * 60, 17 * 60),

        # Douglas's busy times: 9:00-11:30 and 12:00-16:30
        (9 * 60, 11 * 60 + 30),
        (12 * 60, 16 * 60 + 30),

        # Ryan's busy times: 9:00-9:30, 13:00-14:00 and 14:30-17:00
        (9 * 60, 9 * 60 + 30),
        (13 * 60, 14 * 60),
        (14 * 60 + 30, 17 * 60)
    ]

    # Add non-overlapping constraints for each busy period.
    for b_start, b_end in busy_intervals:
        s.add(no_overlap(b_start, b_end))

    # Check for satisfiability.
    if s.check() == sat:
        m = s.model()
        start_val = m[meeting_start].as_long()
        end_val = start_val + duration
        # Output the day and the meeting time in HH:MM:HH:MM format.
        print("Monday")
        print(f"{minutes_to_str(start_val)}:{minutes_to_str(end_val)}")
    else:
        print("No valid meeting time found.")

if __name__ == "__main__":
    main()