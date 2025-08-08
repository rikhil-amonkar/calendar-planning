def minutes_to_time(minutes):
    """Convert minutes since midnight to HH:MM format."""
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

def is_conflict(start, end, blocks):
    """
    Check if the meeting interval [start, end) overlaps with any blocked intervals.
    Each block is a tuple (block_start, block_end) where times are in minutes.
    """
    for block_start, block_end in blocks:
        # Overlap exists if the meeting starts before the block ends 
        # and ends after the block starts.
        if start < block_end and end > block_start:
            return True
    return False

def find_meeting():
    meeting_duration = 30  # 30 minutes duration

    # Define work hours: Monday 9:00 to 17:00,
    # but Helen cannot meet after 15:00, meaning the meeting must finish by 15:00.
    work_start = 9 * 60        # 09:00 -> 540 minutes
    work_end = 15 * 60         # 15:00 -> 900 minutes (meeting_end must be <= 900)

    # Define the blocked time intervals (in minutes since midnight)
    # Christine's blocked intervals
    christine_blocks = [
        (11 * 60, 11 * 60 + 30),   # 11:00 - 11:30 -> 660 to 690
        (15 * 60, 15 * 60 + 30)    # 15:00 - 15:30 -> 900 to 930 (outside our window anyway)
    ]

    # Helen's blocked intervals
    helen_blocks = [
        (9 * 60 + 30, 10 * 60 + 30),    # 09:30 - 10:30 -> 570 to 630
        (11 * 60, 11 * 60 + 30),        # 11:00 - 11:30 -> 660 to 690
        (12 * 60, 12 * 60 + 30),        # 12:00 - 12:30 -> 720 to 750
        (13 * 60 + 30, 16 * 60),        # 13:30 - 16:00 -> 810 to 960
        (16 * 60 + 30, 17 * 60)         # 16:30 - 17:00 -> 990 to 1020
    ]

    # Loop over possible start times (in minutes) within the available time window.
    # Ensure meeting_end = meeting_start + meeting_duration does not exceed work_end (900 minutes)
    for meeting_start in range(work_start, work_end - meeting_duration + 1):
        meeting_end = meeting_start + meeting_duration

        # Check if the meeting slot conflicts with any participant's blocked intervals.
        if (not is_conflict(meeting_start, meeting_end, christine_blocks) and
                not is_conflict(meeting_start, meeting_end, helen_blocks)):
            # Valid meeting slot found.
            start_str = minutes_to_time(meeting_start)
            end_str = minutes_to_time(meeting_end)
            return "Monday", f"{start_str}:{end_str}"

    # If no valid meeting slot is found, return None.
    return None, None

if __name__ == "__main__":
    day, time_range = find_meeting()
    if day and time_range:
        print(f"{day}, {time_range}")
    else:
        print("No available meeting slot found.")