from z3 import *

def main():
    # Create a Z3 solver instance
    s = Solver()

    # Meeting duration in minutes.
    meeting_duration = 30

    # We measure time in minutes relative to 9:00.
    # Office hours: 9:00 (0 minutes) to 17:00 (480 minutes).
    # Also, because the meeting lasts 30 minutes, the meeting must start no later than 450.
    # Janice prefers not to meet after 13:00, i.e. meeting start must be before 13:00,
    # which is 13:00 - 9:00 = 240 minutes.
    meeting_start = Int('meeting_start')
    s.add(meeting_start >= 0, meeting_start <= 450)
    s.add(meeting_start < 240)  # Janice's preference

    # Each participant's busy schedule is given as intervals in HH:MM (relative to 9:00).
    # We convert each busy interval to minutes relative to 9:00.
    #
    # For example:
    #   9:30 to 10:30 becomes [30, 90]
    #   12:00 to 12:30 becomes [180, 210]
    #
    # The meeting [meeting_start, meeting_start+30] must not overlap any busy interval.
    # Two intervals [a,b] and [c,d] do not overlap if (a+duration <= c) or (a >= d).

    busy_intervals = [
        # Christine's busy periods
        (30, 90),    # 9:30-10:30
        (180, 210),  # 12:00-12:30
        (240, 270),  # 13:00-13:30
        (330, 360),  # 14:30-15:00
        (420, 450),  # 16:00-16:30

        # Bobby's busy periods
        (180, 210),  # 12:00-12:30
        (330, 360),  # 14:30-15:00

        # Elizabeth's busy periods
        (0, 30),     # 9:00-9:30
        (150, 240),  # 11:30-13:00
        (270, 300),  # 13:30-14:00
        (360, 390),  # 15:00-15:30
        (420, 480),  # 16:00-17:00

        # Tyler's busy periods
        (0, 120),    # 9:00-11:00
        (180, 210),  # 12:00-12:30
        (240, 270),  # 13:00-13:30
        (390, 420),  # 15:30-16:00
        (450, 480),  # 16:30-17:00

        # Edward's busy periods
        (0, 30),     # 9:00-9:30
        (60, 120),   # 10:00-11:00
        (150, 300),  # 11:30-14:00
        (330, 390),  # 14:30-15:30
        (420, 480),  # 16:00-17:00
    ]

    # For each busy interval, add the constraint that the meeting does not overlap it.
    for bstart, bend in busy_intervals:
        # The meeting [meeting_start, meeting_start+30] must either finish
        # on or before the busy interval begins, or start on/after the busy interval ends.
        s.add(Or(meeting_start + meeting_duration <= bstart, meeting_start >= bend))

    if s.check() == sat:
        m = s.model()
        start_offset = m[meeting_start].as_long()
        # Convert the meeting start back to absolute time (minutes since midnight).
        # 9:00 AM is 9*60 = 540.
        start_total = 540 + start_offset
        end_total = start_total + meeting_duration

        start_hour = start_total // 60
        start_min = start_total % 60
        end_hour = end_total // 60
        end_min = end_total % 60

        # Format the time as HH:MM where each field is zero-padded.
        start_time_str = f"{start_hour:02d}:{start_min:02d}"
        end_time_str   = f"{end_hour:02d}:{end_min:02d}"
        # Output in the required format with the day of the week.
        print(f"Monday {{{start_time_str}:{end_time_str}}}")
    else:
        print("No valid meeting time found.")

if __name__ == "__main__":
    main()